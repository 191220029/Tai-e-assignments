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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.dataflow.inter.InterConstantPropagation;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;

import java.util.concurrent.atomic.AtomicBoolean;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        // Init IR's parameters' val as NAC
        CPFact fact = new CPFact();
        cfg.getIR().getParams().forEach(
                param -> {
                    if (canHoldInt(param)) {
                        fact.update(param, Value.getNAC());
                    }
                }
        );
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach(
                (param, value) -> {
                    var target_value = target.get(param);
                    target.update(param, this.meetValue(value, target_value));
                }
        );
    }

    /**
     * Meets two Values.
     */
    public static Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }

        if (v1.isConstant() && v2.isConstant()) {
            if (v1.equals(v2)) {
                return Value.makeConstant(v1.getConstant());
            }
            else {
                return Value.getNAC();
            }
        }

        if (v1.isConstant() && v2.isUndef()) {
            return Value.makeConstant(v1.getConstant());
        }
        if (v1.isUndef() && v2.isConstant()) {
            return Value.makeConstant(v2.getConstant());
        }

        return Value.getUndef();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        AtomicBoolean changed = new AtomicBoolean(false);
        in.forEach(
                (param, value) -> {
                    changed.set(out.update(param, value) | changed.get());
                }
        );

        // Calculate the result for definition statement with int var left value only.
        if (stmt instanceof DefinitionStmt<?,?> def) {
            if (def.getLValue() instanceof Var v && canHoldInt(v)) {
                var old_value = in.copy().get(v);

                var result = evaluate(def.getRValue(), in);
                out.update(v, result);

                changed.set((!old_value.equals(result)) | changed.get());
            }
        }

        return changed.get();
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }

        if (exp instanceof Var var) {
            return in.get(var);
        }

        if (exp instanceof BinaryExp binaryExp) {
            var op_1 = evaluate(binaryExp.getOperand1(), in);
            var op_2 = evaluate(binaryExp.getOperand2(), in);
            var op = binaryExp.getOperator();

            // handle div0 exception
            if (op instanceof ArithmeticExp.Op aop
                    && (aop == ArithmeticExp.Op.DIV || aop == ArithmeticExp.Op.REM)
                    && op_2.isConstant()
                    && op_2.getConstant() == 0
            ) {
                return Value.getUndef();
            }

            // evaluate result of binary expression
            if (op_1.isConstant() && op_2.isConstant()) {
                var var_1 = op_1.getConstant();
                var var_2 = op_2.getConstant();

                if (op instanceof ArithmeticExp.Op aop) {
                    switch (aop) {
                        case ADD -> {
                            return Value.makeConstant(var_1 + var_2);
                        }
                        case SUB -> {
                            return Value.makeConstant(var_1 - var_2);
                        }
                        case MUL -> {
                            return Value.makeConstant(var_1 * var_2);
                        }
                        case DIV -> {
                            return Value.makeConstant(var_1 / var_2);
                        }
                        case REM -> {
                            return Value.makeConstant(var_1 % var_2);
                        }
                    }
                }

                else if (op instanceof ConditionExp.Op cop) {
                    switch (cop) {
                        case EQ -> {
                            return Value.makeConstant(var_1 == var_2 ? 1 : 0);
                        }
                        case NE -> {
                            return Value.makeConstant(var_1 != var_2 ? 1 : 0);
                        }
                        case LT -> {
                            return Value.makeConstant(var_1 < var_2 ? 1 : 0);
                        }
                        case GT -> {
                            return Value.makeConstant(var_1 > var_2 ? 1 : 0);
                        }
                        case LE -> {
                            return Value.makeConstant(var_1 <= var_2 ? 1 : 0);
                        }
                        case GE -> {
                            return Value.makeConstant(var_1 >= var_2 ? 1 : 0);
                        }
                    }
                }

                else if (op instanceof ShiftExp.Op sop) {
                    switch (sop) {
                        case SHL -> {
                            return Value.makeConstant(var_1 << var_2);
                        }
                        case SHR -> {
                            return Value.makeConstant(var_1 >> var_2);
                        }
                        case USHR -> {
                            return Value.makeConstant(var_1 >>> var_2);
                        }
                    }
                }

                else if (op instanceof BitwiseExp.Op bop) {
                    switch (bop) {
                        case OR -> {
                            return Value.makeConstant(var_1 | var_2);
                        }
                        case AND -> {
                            return Value.makeConstant(var_1 & var_2);
                        }
                        case XOR -> {
                            return Value.makeConstant(var_1 ^ var_2);
                        }
                    }
                }
            }


            else if (op_1.isNAC() || op_2.isNAC()) {
                return Value.getNAC();
            }
            // other cases of op
            return Value.getUndef();
        }


        if (exp instanceof StaticFieldAccess staticFieldAccess) {
            return InterConstantPropagation.values.getOrDefault(
                    new Pair<>(
                            staticFieldAccess.getFieldRef().getDeclaringClass(),
                            staticFieldAccess.getFieldRef()
                    ),
                    Value.getUndef()
            );
        }

        if (exp instanceof InstanceFieldAccess instanceFieldAccess) {
            var pts = InterConstantPropagation.pta.getPointsToSet(instanceFieldAccess.getBase());
            var value = Value.getUndef();

            for (var obj: pts) {
                value = meetValue(
                    value,
                    InterConstantPropagation.values.getOrDefault(
                            new Pair<>(obj, instanceFieldAccess.getFieldRef()),
                            Value.getUndef()
                    )
                );
            }

            return value;
        }

        if (exp instanceof ArrayAccess arrayAccess) {
            var index = evaluate(arrayAccess.getIndex(), in);

            if (index.isNAC()) {
                var value = Value.getUndef();
                for (var obj: InterConstantPropagation.pta.getPointsToSet(arrayAccess.getBase())) {
                    for (var entry: InterConstantPropagation.values.entrySet()) {
                        if (obj.equals(entry.getKey().first())
                         && entry.getKey().second() instanceof Value) {
                            value = meetValue(value, entry.getValue());
                        }
                    }
                }
                return value;
            }

            if (index.isConstant()) {
                var value = Value.getUndef();
                for (var obj: InterConstantPropagation.pta.getPointsToSet(arrayAccess.getBase())) {
                    value = meetValue(
                            value,
                            InterConstantPropagation.values.getOrDefault(
                                    new Pair<>(obj, index),
                                    Value.getUndef()
                            )
                    );
                    value = meetValue(
                            value,
                            InterConstantPropagation.values.getOrDefault(
                                    new Pair<>(obj, Value.getNAC()),
                                    Value.getUndef()
                            )
                    );
                }
                return value;
            }

            return Value.getUndef();
        }

        // other cases of statements
        return Value.getNAC();
    }
}