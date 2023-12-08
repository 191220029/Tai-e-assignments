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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        // if c:m \notin RM then
        if (!this.callGraph.contains(csMethod)) {
            // add c:m to RM
            this.callGraph.addReachableMethod(csMethod);
            // S=S\cup S_m
            // foreach i: x = new T() \in S_m
            // add <c:x, {c:oi}> to WL
            // foreach x = y \in S_m do
            // AddEdge(c:y, c:x)
            csMethod.getMethod().getIR().forEach(
                    stmt -> stmt.accept(new StmtProcessor(csMethod))
            );
        }

    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me


        @Override
        public Void visit(New stmt) {
            var lptr = csManager.getCSVar(this.context, stmt.getLValue());
            var heap_obj = heapModel.getObj(stmt);

            workList.addEntry(
                    lptr,
                    PointsToSetFactory.make(csManager.getCSObj(
                            contextSelector.selectHeapContext(this.csMethod, heap_obj),
                            heap_obj
                    ))
            );
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    csManager.getCSVar(this.context, stmt.getRValue()),
                    csManager.getCSVar(this.context, stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        csManager.getStaticField(stmt.getFieldRef().resolve()),
                        csManager.getCSVar(this.context, stmt.getLValue())
                );
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        csManager.getCSVar(this.context, stmt.getRValue()),
                        csManager.getStaticField(stmt.getFieldRef().resolve())
                );
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                processCallRemaining(
                        csManager.getCSMethod(
                                contextSelector.selectContext(
                                        csManager.getCSCallSite(this.context, stmt),
                                        resolveCallee(null, stmt)
                                ),
                                resolveCallee(null, stmt)
                        ),
                        csManager.getCSCallSite(this.context, stmt)
                );
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        // if s-> t \notin PFG then
        //  add s->t to PFG
        if (!this.pointerFlowGraph.getSuccsOf(source).contains(target)) {
            this.pointerFlowGraph.addEdge(source, target);

            // if pt(s) is not empty then
            //  add <t, pt(s)> to WL
            if (!source.getPointsToSet().isEmpty()) {
                this.workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        // while WL is not empty do
        while (!this.workList.isEmpty()) {
            // remove <n, pts> from WL
            var work_node = this.workList.pollEntry();
            var n = work_node.pointer();
            var pts = work_node.pointsToSet();

            // \Delta = propagate(n, pt(s))
            var delta = this.propagate(n, pts);

            // if n represents a variable c:x then
            if (n instanceof CSVar ptr) {
                // foreach c':oi \in \Delta do
                Var v = ptr.getVar();
                Context context = ptr.getContext();

                delta.forEach(csObj -> {
                    // Load
                    v.getLoadFields().forEach(loadField -> addPFGEdge(
                            this.csManager.getInstanceField(csObj, loadField.getFieldRef().resolve()),
                            this.csManager.getCSVar(context, loadField.getLValue())
                    ));
                    // Load array
                    v.getLoadArrays().forEach(loadArray -> addPFGEdge(
                            this.csManager.getArrayIndex(csObj),
                            this.csManager.getCSVar(context, loadArray.getLValue())
                    ));
                    // Store
                    v.getStoreFields().forEach(storeField -> addPFGEdge(
                            this.csManager.getCSVar(context, storeField.getRValue()),
                            this.csManager.getInstanceField(csObj, storeField.getFieldRef().resolve())
                    ));
                    // Store array
                    v.getStoreArrays().forEach(storeArray -> addPFGEdge(
                            this.csManager.getCSVar(context, storeArray.getRValue()),
                            this.csManager.getArrayIndex(csObj)
                    ));

                    processCall(ptr, csObj);
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
        // \Delta = pts - pt(n)
        var delta = PointsToSetFactory.make();
        pointsToSet.getObjects().stream().filter(csObj -> !pointer.getPointsToSet().contains(csObj))
                .forEach(delta::addObject);

        // if pts is not empty then
        if (!delta.isEmpty()) {
            // pt(n) = pt(n)\Union pts
            delta.forEach(csObj -> pointer.getPointsToSet().addObject(csObj));
            // foreach n->s \in PFG do
            //  add <s, pts> to WL
            this.pointerFlowGraph.getSuccsOf(pointer).forEach(s -> this.workList.addEntry(s, delta));
        }

        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        // foreach l: r = x.k(a_1,\cdots,a_n)\in S do
        recv.getVar().getInvokes().forEach(invoke -> {
            // m = Dispatch(o_i, k)
            var m = resolveCallee(recvObj, invoke);
            // c^t = Select(c, l, c': o_i)
            var ct = this.contextSelector.selectContext(
                    csManager.getCSCallSite(recv.getContext(), invoke),
                    recvObj,
                    m
            );
            // add <c^t: m_this, {c': o_i}> to WL
            this.workList.addEntry(
                    this.csManager.getCSVar(ct, m.getIR().getThis()),
                    PointsToSetFactory.make(recvObj)
            );

            processCallRemaining(
                    this.csManager.getCSMethod(ct, m),
                    this.csManager.getCSCallSite(recv.getContext(), invoke)
            );
        });
    }

    private void processCallRemaining(CSMethod callee, CSCallSite callSite) {
        // if c:l -> c^t: m\notin CG then
        if (!this.callGraph.getCalleesOf(callSite).contains(callee)) {
            CallKind kind = null;
            if (callSite.getCallSite().isVirtual()) {
                kind = CallKind.VIRTUAL;
            }
            else if (callSite.getCallSite().isStatic()) {
                kind = CallKind.STATIC;
            }
            else if (callSite.getCallSite().isInterface()) {
                kind = CallKind.INTERFACE;
            }
            else if (callSite.getCallSite().isSpecial()) {
                kind = CallKind.SPECIAL;
            }
            else if (callSite.getCallSite().isDynamic()) {
                kind = CallKind.DYNAMIC;
            }

            if (kind != null) {
                // add <c:l -> c^t:m to CG>
                this.callGraph.addEdge(new Edge<>(kind, callSite, callee));
                // AddReachable(c^t: m)
                this.addReachable(callee);

                var c = callSite.getContext();
                var ct = callee.getContext();

                // foreach parameter p_i of m do
                var args = callee.getMethod().getIR().getParams();
                for (int i = 0; i < args.size(); i++) {
                    // AddEdge(c: a_i, c^t: p_i)
                    this.addPFGEdge(
                            this.csManager.getCSVar(c, callSite.getCallSite().getRValue().getArg(i)),
                            this.csManager.getCSVar(ct, args.get(i))
                    );
                }

                // AddEdge(c^t: m_{ret}, c:r)
                if (callSite.getCallSite().getLValue() != null) {
                    callee.getMethod().getIR().getReturnVars().forEach(var -> addPFGEdge(
                            this.csManager.getCSVar(ct, var),
                            this.csManager.getCSVar(c, callSite.getCallSite().getLValue())
                    ));
                }
            }
        }

    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
