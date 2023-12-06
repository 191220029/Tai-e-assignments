/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        // if m \notin RM then
        if (!callGraph.contains(method)) {
            // add m to RM
            // S \cup = S_m
            callGraph.addReachableMethod(method);
            method.getIR().getStmts().forEach(stmt -> {
                // StmtProcessor will do the remaining analysis.
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        /// stmt: i: x = new T()
        /// rule: / o_i \in pt(x)
        public Void visit(New stmt) {
            var x = stmt.getLValue();
            var p = pointerFlowGraph.getVarPtr(x);
            workList.addEntry(p, new PointsToSet(heapModel.getObj(stmt)));

            return null;
        }

        @Override
        /// stmt: r = x.k(a_1,...,a_n)
        public Void visit(Invoke call_site) {
            if (call_site.isStatic()) {
                // Dispatch. `recv` ignored under static call_site.
                var callee = resolveCallee(null, call_site);

                CallKind call_kind = getCallKind(call_site);

                // Filter out dynamic calls.
                if (call_kind == null) {
                    return null;
                }
                // Update call graph.
                // if l \rightarrow m \notin CG then
                if(!callGraph.getCalleesOf(call_site).contains(callee)) {
                    // add l \rightarrow m to CG
                    // AddReachable(m)
                    callGraph.addEdge(new Edge<>(call_kind, call_site, callee));
                    addReachable(callee);

                    // foreach parameter p_i of m do
                    for(int i = 0; i < call_site.getRValue().getArgs().size(); i++) {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(call_site.getRValue().getArg(i)),
                                pointerFlowGraph.getVarPtr(callee.getIR().getParam(i))
                        );
                    }

                    // AddEdge(m_{ret}, r)
                    if (call_site.getLValue() == null) {
                        return null;
                    }
                    callee.getIR().getReturnVars().forEach(
                            m_ret -> {
                                addPFGEdge(
                                        pointerFlowGraph.getVarPtr(m_ret),
                                        pointerFlowGraph.getVarPtr(call_site.getLValue())
                                );
                            }
                    );
                }
            }

            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()){
                addPFGEdge(
                        pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()),
                        pointerFlowGraph.getVarPtr(stmt.getLValue())
                );
            }
            return null;
        }

        @Override
        public Void visit(StoreField storeField) {
            if(storeField.isStatic()) {
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(storeField.getRValue()),
                        pointerFlowGraph.getStaticField(storeField.getFieldRef().resolve())
                );
            }
            return null;
        }
        private static CallKind getCallKind(Invoke call_site) {
            CallKind call_kind = null;

            if (call_site.isVirtual()) {
                call_kind = CallKind.VIRTUAL;
            }
            if (call_site.isStatic()) {
                call_kind = CallKind.STATIC;
            }
            if (call_site.isSpecial()) {
                call_kind = CallKind.SPECIAL;
            }
            if (call_site.isInterface()) {
                call_kind = CallKind.INTERFACE;
            }
            return call_kind;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        // if s \rightarrow t \notin PFG then
        if (!pointerFlowGraph.getSuccsOf(source).contains(target)) {
            //  add s \rightarrow t to PFG
            pointerFlowGraph.addEdge(source, target);

            // if pt(s) is not empty then
            //  add <t, pt(s)> to WL
            var pts = source.getPointsToSet();
            if (!pts.isEmpty()) {
                workList.addEntry(target, pts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        // while WL is not empty do
        while (!workList.isEmpty()) {
            // remove <n, pts> from WL
            var entry = workList.pollEntry();
            var n = entry.pointer();
            var pts = entry.pointsToSet();

            // delta = propagate(n, pts)
            var delta = propagate(n, pts);

            // if n represents a variable x then
            if (n instanceof VarPtr vptr) {
                var x = vptr.getVar();

                // foreach o_i \in \delta do
                delta.forEach(obj -> {
                    // foreach x.f = y \in S do
                    //  AddEdge(y, o_i.f)
                    x.getStoreFields().forEach(
                            storeField -> addPFGEdge(
                                    pointerFlowGraph.getVarPtr(storeField.getRValue()),
                                    pointerFlowGraph.getInstanceField(obj, storeField.getFieldAccess().getFieldRef().resolve())
                            ));

                    // foreach x[*] = y \in S do
                    //  AddEdge(y, x[*])
                    x.getStoreArrays().forEach(
                            storeArray -> addPFGEdge(
                                    pointerFlowGraph.getVarPtr(storeArray.getRValue()),
                                    pointerFlowGraph.getArrayIndex(obj)
                            ));

                    // foreach y = x.f \in S do
                    //  AddEdge(o_i.f, y)
                    x.getLoadFields().forEach(
                            loadField -> addPFGEdge(
                                    pointerFlowGraph.getInstanceField(obj, loadField.getFieldAccess().getFieldRef().resolve()),
                                    pointerFlowGraph.getVarPtr(loadField.getLValue())
                            )
                    );

                    // foreach y = x[*] \in S do
                    //  AddEdge(x[*], y)
                    x.getLoadArrays().forEach(
                            loadArray -> addPFGEdge(
                                    pointerFlowGraph.getArrayIndex(obj),
                                    pointerFlowGraph.getVarPtr(loadArray.getLValue())
                            )
                    );

                    // ProcessCall(x, o_i)
                    processCall(x, obj);
                });

            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        var ptn = pointer.getPointsToSet();

        // delta = pts - pt(n)
        var delta = new PointsToSet();
        pointsToSet.objects()
                .filter(obj -> !ptn.contains(obj))
                .forEach(delta::addObject);

        // if delta is not empty then
        if (!delta.isEmpty()) {
            // pt(n) \cup= delta
            delta.forEach(ptn::addObject);

            // foreach n \rightarrow s \in PFG do
            //  add <s, delta> to WL
            pointerFlowGraph.getSuccsOf(pointer)
                    .forEach(s -> workList.addEntry(s, delta));
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        // foreach l: r = x.k(a_1,...,a_n) \in S do
        var.getInvokes().forEach(
                invoke -> {
                    // m = dispatch(o_i, k)
                    // add <m_this, \{o_i\}> to WL
                    var callee = resolveCallee(recv, invoke);
                    workList.addEntry(
                            pointerFlowGraph.getVarPtr(callee.getIR().getThis()),
                            new PointsToSet(recv)
                    );

                    CallKind call_kind = null;

                    if (invoke.isVirtual()) {
                        call_kind = CallKind.VIRTUAL;
                    }
                    if (invoke.isStatic()) {
                        call_kind = CallKind.STATIC;
                    }
                    if (invoke.isSpecial()) {
                        call_kind = CallKind.SPECIAL;
                    }
                    if (invoke.isInterface()) {
                        call_kind = CallKind.INTERFACE;
                    }

                    // Filter out dynamic calls.
                    if (call_kind != null) {
                        if(!callGraph.getCalleesOf(invoke).contains(callee)) {
                            // add l \rightarrow m to CG
                            // AddReachable(m)
                            callGraph.addEdge(new Edge<>(call_kind, invoke, callee));
                            addReachable(callee);

                            // foreach parameter p_i of m do
                            for(int i = 0; i < invoke.getRValue().getArgs().size(); i++) {
                                addPFGEdge(
                                        pointerFlowGraph.getVarPtr(invoke.getRValue().getArg(i)),
                                        pointerFlowGraph.getVarPtr(callee.getIR().getParam(i))
                                );
                            }

                            // AddEdge(m_{ret}, r)
                            if (invoke.getLValue() != null) {
                                callee.getIR().getReturnVars().forEach(
                                        m_ret -> {
                                            addPFGEdge(
                                                    pointerFlowGraph.getVarPtr(m_ret),
                                                    pointerFlowGraph.getVarPtr(invoke.getLValue())
                                            );
                                        }
                                );
                            }
                        }
                    }
                }
        );
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
