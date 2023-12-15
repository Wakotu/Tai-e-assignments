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

import java.util.ArrayDeque;
import java.util.NoSuchElementException;
import java.util.Queue;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends AbstractDataflowAnalysis<Stmt, SetFact<Var>> {
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
    return new SetFact<>();
  }

  @Override
  public SetFact<Var> newInitialFact() {
    return new SetFact<>();
  }

  @Override
  public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
    /**
     * A method to handle control flow merge
     * Basic idea: merge the new fact
     */
    // WARN: need to handle the null pointer situation?
    target.union(fact);
  }

  @Override
  public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
    /**
     * Need to realize that this transformation is based on statement.
     * the key transferring idea is remove definition and removes use-before-def in
     * BB
     * Note that a statement could not define and use a variable at the same
     * time.(guess)
     * Over stmt, just remove def and simply add uses
     */

    // WARN: need to handle the null pointer situation?
    in.union(out);

    // get the def element
    Var def = null;
    try {
      LValue v = stmt.getDef().get();
      if (v instanceof Var) {
        def = (Var) v;
      }
    } catch (NoSuchElementException e) {
    }
    if (def != null)
      in.remove(def);

    // get uses
    var uses = stmt.getUses();
    // basic idea: check if element of uses is Var and add its subexpressions to the
    // pool
    Queue<RValue> q = new ArrayDeque<>();
    // initialize the queue
    for (var use : uses) {
      q.add(use);
    }

    while (!q.isEmpty()) {
      var exp = q.remove();
      if (exp instanceof Var) {
        // handle `use` in factset
        in.add((Var) exp);
      } else {
        // if exp is not a compound expression, code below would have no effect
        for (var sub : exp.getUses()) {
          q.add(sub);
        }
      }
    }

    return false;
  }
}
