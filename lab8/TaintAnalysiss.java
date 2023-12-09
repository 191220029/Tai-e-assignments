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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Pair;

import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me
    public Obj discover_taint_source(JMethod m, Invoke invoke) {
        return config.getSources().contains(new Source(m, m.getReturnType())) ?
                manager.makeTaint(invoke, m.getReturnType()) :
                null;
    }

    public Set<Pair<Var, Obj>> discover_taint(CSVar base, CSCallSite csCallSite, JMethod m) {
        var taints = new HashSet<Pair<Var, Obj>>();

        taints.addAll(this.discover_taint_base2result(base, csCallSite, m));
        taints.addAll(this.discover_taint_param2base(base, csCallSite, m));
        taints.addAll(this.discover_taint_param2result(csCallSite, m));

        return taints;
    }

    private Set<Pair<Var, Obj>> discover_taint_base2result(CSVar base, CSCallSite csCallSite, JMethod m) {
        var pta = solver.getResult();
        var recv_var = csCallSite.getCallSite().getLValue();
        var ret_type = m.getReturnType();
        var taints = new HashSet<Pair<Var, Obj>>();

        if (base != null) {
            if (recv_var != null) {
                var taint_transfer = new TaintTransfer(
                        m,
                        TaintTransfer.BASE,
                        TaintTransfer.RESULT,
                        m.getReturnType()
                );

                if (config.getTransfers().contains(taint_transfer)) {
                    pta.getPointsToSet(base).stream()
                            .filter(csObj -> manager.isTaint(csObj.getObject()))
                            .forEach(csObj -> taints.add(new Pair<>(
                                    recv_var,
                                    manager.makeTaint(
                                            manager.getSourceCall(csObj.getObject()),
                                            ret_type
                                    )
                            )));
                }
            }
        }

        return taints;
    }

    private Set<Pair<Var, Obj>> discover_taint_param2base(CSVar base, CSCallSite csCallSite, JMethod m) {
        var pta = solver.getResult();
        var taints = new HashSet<Pair<Var, Obj>>();

        if (base != null) {
            var base_type = base.getType();
            var args = csCallSite.getCallSite().getInvokeExp().getArgs();

            for (int i = 0; i < args.size(); i++) {
                var taint_transfer = new TaintTransfer(
                        m,
                        i,
                        TaintTransfer.BASE,
                        base_type
                );

                if (config.getTransfers().contains(taint_transfer)) {
                    pta.getPointsToSet(csManager.getCSVar(
                                    csCallSite.getContext(),
                                    args.get(i)
                            )).stream().filter(csObj -> manager.isTaint(csObj.getObject()))
                            .forEach(csObj -> taints.add(new Pair<>(
                                    base.getVar(),
                                    manager.makeTaint(
                                            manager.getSourceCall(csObj.getObject()),
                                            base_type
                                    )
                            )));
                }
            }
        }

        return taints;
    }

    private Set<Pair<Var, Obj>> discover_taint_param2result(CSCallSite csCallSite, JMethod m) {
        var pta = solver.getResult();
        var recv_var = csCallSite.getCallSite().getLValue();
        var ret_type = m.getReturnType();
        var taints = new HashSet<Pair<Var, Obj>>();
        var args = csCallSite.getCallSite().getInvokeExp().getArgs();

        for (int i = 0; i < args.size(); i++) {
            var taint_transfer = new TaintTransfer(
                    m,
                    i,
                    TaintTransfer.RESULT,
                    ret_type
            );

            if (config.getTransfers().contains(taint_transfer)) {
                pta.getPointsToSet(csManager.getCSVar(
                                csCallSite.getContext(),
                                args.get(i)
                        )).stream().filter(csObj -> manager.isTaint(csObj.getObject()))
                        .forEach(csObj -> taints.add(new Pair<>(
                                recv_var,
                                manager.makeTaint(
                                        manager.getSourceCall(csObj.getObject()),
                                        ret_type
                                )
                        )));
            }
        }

        return taints;
    }

    public boolean is_taint(CSObj csObj) {
        return manager.isTaint(csObj.getObject());
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.

        var cs_call_graph = result.getCSCallGraph();

        cs_call_graph.reachableMethods().forEach(
                csMethod ->
                    cs_call_graph.getCallersOf(csMethod).forEach(csCallSite ->  {
                        var args = csCallSite.getCallSite().getInvokeExp().getArgs();
                        for(int i = 0; i < args.size(); i++) {
                            var sink = new Sink(csMethod.getMethod(), i);

                            if (config.getSinks().contains(sink)) {
                                var index = i;
                                result.getPointsToSet(args.get(i))
                                        .stream().filter(manager::isTaint)
                                        .forEach(obj -> taintFlows.add(new TaintFlow(
                                                manager.getSourceCall(obj),
                                                csCallSite.getCallSite(),
                                                index
                                        )));
                            }
                        }
                    })
        );

        return taintFlows;
    }

}