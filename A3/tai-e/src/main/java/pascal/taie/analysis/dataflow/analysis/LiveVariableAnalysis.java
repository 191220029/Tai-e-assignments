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

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        return new SetFact<>();
    }

    @Override
    public SetFact<Var> newInitialFact() {
        // TODO - finish me
        return new SetFact<>();
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // TODO - finish me
        target.union(fact);
    }

    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // TODO - finish me
        // IN[B] = useB U (OUT[B] - defB)

        SetFact<Var> new_in = new SetFact<Var>();
        new_in.set(out);
        // 1. If defB defines a valid Var, Then do OUT[B] - defB
        if (stmt.getDef().isPresent() && stmt.getDef().get() instanceof Var) {
            new_in.remove((Var) stmt.getDef().get());
        }

        // 2. do useB U (OUT[B] - defB)
        //    Add v to new_in if v in useB and v is typeof Var
        stmt.getUses().forEach(rValue -> {
            if (rValue instanceof Var) {
                new_in.add((Var) rValue);
            }
        });

        // 3. If new_in equals IN[B], return false;
        //    else do IN[B] = useB U (OUT[B] - defB), return true;
        if (new_in.equals(in)) {
            return false;
        }
        in.set(new_in);
        return true;
    }
}
