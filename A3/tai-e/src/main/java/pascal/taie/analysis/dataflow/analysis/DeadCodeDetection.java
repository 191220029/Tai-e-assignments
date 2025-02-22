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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        // Collect all livecode in current cfg, then we have deadcode = all \ (livecode + exit).
        Set<Stmt> live_code = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        Queue<Stmt> stmt_queue = new LinkedList<>();
        stmt_queue.add(cfg.getEntry());

        while(!stmt_queue.isEmpty()){
            var stmt = stmt_queue.poll();

            // Assignment statements with dead left value but has no side effect shall be eliminated.
            // If not, go to check all its successors.
            if (stmt instanceof AssignStmt<?,?> assignStmt && assignStmt.getLValue() instanceof Var var) {
                if(!liveVars.getResult(stmt).contains(var) && hasNoSideEffect(assignStmt.getRValue())) {
                    stmt_queue.addAll(cfg.getSuccsOf(stmt));
                    continue;
                }
            }

            // If such statement is not dead, then mark it as live code.
            // If such statement is already marked as live, skip this stmt.
            if(!live_code.add(stmt)) {
                continue;
            }

            // Check code in if clauses.
            if (stmt instanceof If ifStmt) {
                // Try to evaluate condition's result if it is a constant.
                var cond = ConstantPropagation.evaluate(
                        ifStmt.getCondition(),
                        constants.getInFact(stmt)
                );

                if (cond.isConstant()) {
                    // Check inner code if any branch is reachable.
                    cfg.getOutEdgesOf(stmt).forEach(
                            stmtEdge -> {
                                if (
                                        (stmtEdge.getKind() == Edge.Kind.IF_TRUE && cond.getConstant() == 1)
                                        || (stmtEdge.getKind() == Edge.Kind.IF_FALSE && cond.getConstant() == 0)
                                ) {
                                    stmt_queue.add(stmtEdge.getTarget());
                                }
                            }
                    );
                }
                // Check all branches when condition is NAC.
                else {
                    stmt_queue.addAll(cfg.getSuccsOf(stmt));
                }
            }

            // Check code in switch-case clauses.
            else if (stmt instanceof SwitchStmt switchStmt) {
                var switch_cond = ConstantPropagation.evaluate(
                        switchStmt.getVar(),
                        constants.getInFact(stmt)
                );

                // When switch_cond is constant, go to check code in all reachable cases.
                if (switch_cond.isConstant()) {
                    AtomicBoolean has_live_case = new AtomicBoolean(false);
                    switchStmt.getCaseTargets().forEach(
                            case_target -> {
                                if (case_target.first() == switch_cond.getConstant()){
                                    stmt_queue.add(case_target.second());
                                    has_live_case.set(true);
                                }
                            }
                    );

                    // When all cases are unreachable, go to check default case.
                    if (!has_live_case.get()) {
                        stmt_queue.add(switchStmt.getDefaultTarget());
                    }
                }
                // When switch_cond is NAC, all cases will be marked as live, and try to find live code in all cases.
                else
                {
                    stmt_queue.addAll(cfg.getSuccsOf(stmt));
                }
            }

            // For other cases of stmt, mark them as live and go to check all successors.
            else {
                stmt_queue.addAll(cfg.getSuccsOf(stmt));
            }
        }

        // deadcode = all \ (live + exit)
        deadCode.addAll(cfg.getNodes());
        deadCode.remove(cfg.getExit());
        deadCode.removeAll(live_code);

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
