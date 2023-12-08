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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Pair;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public static PointerAnalysisResult pta;

    public static Map<Pair<?, ?>, Value> values = new HashMap<>();
    public static Map<Obj, Set<Var>> alias = new HashMap<>();

    public static Map<Pair<JClass, FieldRef>, Set<LoadField>> static_field_loads = new HashMap<>();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here

        // collect all static field loads.
        this.icfg.getNodes().forEach(stmt -> {
            if (stmt instanceof LoadField loadField && loadField.getFieldAccess() instanceof StaticFieldAccess staticFieldAccess) {
                var index = new Pair<>(staticFieldAccess.getFieldRef().getDeclaringClass(), staticFieldAccess.getFieldRef());
                var loads = static_field_loads.getOrDefault(index, new HashSet<>());
                loads.add(loadField);
                static_field_loads.put(index, loads);
            }
        });

        // collect all aliases
        pta.getVars().forEach(var -> {
            pta.getPointsToSet(var).forEach(obj -> {
                var s = alias.getOrDefault(obj, new HashSet<>());
                s.add(var);
                alias.put(obj, s);
            });
        });
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        AtomicBoolean changed = new AtomicBoolean(false);
        in.forEach((var, value) -> {
            changed.set(changed.get() | out.update(var, value));
        });

        return changed.get();
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        var result_fact = out.copy();

        var return_value = ((Invoke) edge.getSource()).getLValue();
        if (return_value != null) {
            result_fact.remove(return_value);
        }

        return result_fact;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        var return_fact = new CPFact();
        var args = edge.getCallee().getIR().getParams();
        for (int i = 0; i < args.size(); i++) {
            return_fact.update(
                    args.get(i),
                    callSiteOut.get(((Invoke) edge.getSource()).getRValue().getArg(i))
            );
        }

        return return_fact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        var return_fact = new CPFact();
        var return_value = ((Invoke) edge.getCallSite()).getLValue();

        if (return_value != null) {
            edge.getReturnVars()
                    .forEach(var -> return_fact.update(
                            return_value,
                            cp.meetValue(
                                    return_fact.get(return_value),
                                    returnOut.get(var)
                            )
                    ));
        }
        return return_fact;
    }
}