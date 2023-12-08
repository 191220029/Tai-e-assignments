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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.util.collection.Pair;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        this.icfg.forEach(node -> this.result.setOutFact(node, this.analysis.newInitialFact()));

        this.icfg.entryMethods().forEach(method -> result.setOutFact(
                this.icfg.getEntryOf(method),
                this.analysis.newBoundaryFact(this.icfg.getEntryOf(method))
        ));
    }

    private void doSolve() {
        // TODO - finish me
        this.workList = new LinkedList<>(this.icfg.getNodes());

        while(!this.workList.isEmpty()) {
            var node = this.workList.poll();
            var in = (Fact) new CPFact();
            var out = this.result.getOutFact(node);

            // meet in edges
            this.icfg.getInEdgesOf(node).forEach(nodeICFGEdge -> this.analysis.meetInto(
                    this.analysis.transferEdge(nodeICFGEdge, this.result.getOutFact(nodeICFGEdge.getSource())),
                    in
            ));

            // process Store field (static field access + instance field access)
            if ((Stmt) node instanceof StoreField storeField && ConstantPropagation.canHoldInt(storeField.getRValue())) {
                if (storeField.getFieldAccess() instanceof StaticFieldAccess staticFieldAccess) {
                    var key = new Pair<>(staticFieldAccess.getFieldRef().getDeclaringClass(), staticFieldAccess.getFieldRef());
                    var old_value = InterConstantPropagation.values.getOrDefault(
                            key,
                            Value.getUndef()
                    );

                    var meeted_value = this.meetValue(
                            old_value,
                            ConstantPropagation.evaluate(storeField.getRValue(), (CPFact) in)
                    );

                    InterConstantPropagation.values.put(
                            key,
                            meeted_value
                    );

                    if (!meeted_value.equals(old_value)) {
                        InterConstantPropagation.static_field_loads
                                .getOrDefault(key, new HashSet<>())
                                .forEach(loadField -> this.workList.add((Node) loadField));
                    }
                }
                else if (storeField.getFieldAccess() instanceof InstanceFieldAccess instanceFieldAccess) {
                    InterConstantPropagation.pta.getPointsToSet(instanceFieldAccess.getBase()).forEach(obj -> {
                        var key = new Pair<>(obj, instanceFieldAccess.getFieldRef());
                        var old_value = InterConstantPropagation.values.getOrDefault(key, Value.getUndef());

                        var meeted_value = this.meetValue(
                                old_value,
                                ConstantPropagation.evaluate(storeField.getRValue(), (CPFact) in)
                        );

                        if(!meeted_value.equals(old_value)) {
                            InterConstantPropagation.values.put(key, meeted_value);
                            InterConstantPropagation.alias.getOrDefault(obj, new HashSet<>())
                                    .forEach(var -> var.getLoadFields()
                                            .stream().filter(loadField -> storeField.getFieldRef().equals(loadField.getFieldAccess().getFieldRef()))
                                            .forEach(loadField -> workList.add((Node) loadField)));
                        }
                    });
                }
            }
            // process Store array
            if ((Stmt) node instanceof StoreArray storeArray && ConstantPropagation.canHoldInt(storeArray.getRValue())) {
                var index = ConstantPropagation.evaluate(storeArray.getArrayAccess().getIndex(), (CPFact) in);

                if(!index.isUndef()) {
                    InterConstantPropagation.pta.getPointsToSet(storeArray.getArrayAccess().getBase()).forEach(obj -> {
                        var key = new Pair<>(obj, index);
                        var old_value = InterConstantPropagation.values.getOrDefault(key, Value.getUndef());

                        var meeted_value = this.meetValue(
                                old_value,
                                ConstantPropagation.evaluate(storeArray.getRValue(), (CPFact) in)
                        );

                        if(!meeted_value.equals(old_value)) {
                            InterConstantPropagation.values.put(key, meeted_value);
                            InterConstantPropagation.alias.getOrDefault(obj, new HashSet<>())
                                    .forEach(var -> var.getLoadArrays()
                                            .forEach(loadArray -> workList.add((Node) loadArray)));
                        }
                    });
                }
            }

            // If out changed, add successors of node to WL.
            if (this.analysis.transferNode(node, in, out)) {
                workList.addAll(this.icfg.getSuccsOf(node));
            }

            // store facts
            this.result.setInFact(node, in);
            this.result.setOutFact(node, out);
        }
    }

    private Value meetValue(Value a, Value b) {
        if (a.isNAC() || b.isNAC()) {
            return Value.getNAC();
        }

        if (a.isConstant() && b.isConstant()) {
            if (a.equals(b)) {
                return Value.makeConstant(a.getConstant());
            }
            else {
                return Value.getNAC();
            }
        }

        if (a.isConstant() && b.isUndef()) {
            return Value.makeConstant(a.getConstant());
        }
        if (a.isUndef() && b.isConstant()) {
            return Value.makeConstant(b.getConstant());
        }

        return Value.getUndef();
    }
}