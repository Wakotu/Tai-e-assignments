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

import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.NoSuchElementException;
import java.util.Queue;
import java.util.Set;
import java.util.TreeSet;
import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.analysis.graph.cfg.Edge.Kind;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

public class DeadCodeDetection extends MethodAnalysis {
  public static final String ID = "deadcode";

  public DeadCodeDetection(AnalysisConfig config) {
    super(config);
  }

  private static Var extract_def(Stmt stmt) {
    Var def = null;
    try {
      LValue x = stmt.getDef().get();
      if (x instanceof Var)
        def = (Var) x;
    } catch (NoSuchElementException e) {
    }
    return def;
  }

  private static boolean useless(Stmt stmt, DataflowResult<Stmt, SetFact<Var>> liveVars) {
    Var def = extract_def(stmt);
    return !liveVars.getOutFact(stmt).contains(def);
  }

  private static boolean has_side_effect(Stmt stmt) {
    for (var use : stmt.getUses()) {
      if (hasNoSideEffect(use))
        continue;
      return true;
    }
    return false;
  }

  public static int calc(int a, int b, ConditionExp exp) {
    var op = exp.getOperator();
    int res = -1;
    switch (op) {
      case EQ:
        res = a == b ? 1 : 0;
        break;
      case NE:
        res = a != b ? 1 : 0;
        break;
      case LT:
        res = a < b ? 1 : 0;
        break;
      case GT:
        res = a > b ? 1 : 0;
        break;
      case LE:
        res = a <= b ? 1 : 0;
        break;
      case GE:
        res = a >= b ? 1 : 0;
        break;

      default:
        break;
    }
    return res;
  }

  // -1 NAC, 1 for true, 0 for false
  private static Value evaluate(ConditionExp exp, CPFact fact) {
    Value v1 = fact.get(exp.getOperand1()), v2 = fact.get(exp.getOperand2());
    if (v1.isConstant() && v2.isConstant()) {
      int a = v1.getConstant(), b = v2.getConstant();
      return Value.makeConstant(calc(a, b, exp));
    }
    return Value.getNAC();
  }

  private static boolean reachable_if(Value res, Edge<Stmt> e) {
    if (!res.isConstant())
      return true;
    var flag = res.getConstant() == 0 ? false : true;
    switch (e.getKind()) {
      case IF_FALSE:
        flag = !flag;
        break;
      default:
        break;
    }
    return flag;
  }

  private static boolean reachable_switch_case(Value res, Edge<Stmt> e) {
    return res.getConstant() == e.getCaseValue();
  }

  private static void handle_edge(Queue<Stmt> q, Set<Stmt> vis, Edge<Stmt> e) {
    var v = e.getTarget();
    if (vis.contains(v))
      return;
    q.add(v);
    vis.add(v);
  }

  private static void handle_node(Queue<Stmt> q, Set<Stmt> vis, Stmt v) {
    if (vis.contains(v))
      return;
    q.add(v);
    vis.add(v);
  }

  private static Set<Stmt> get_reachable(CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants) {
    // utilize bfs algorithm
    Set<Stmt> vis = new HashSet<>();
    Queue<Stmt> q = new LinkedList<>();
    var u = cfg.getEntry();
    q.add(u);
    vis.add(u);

    while (!q.isEmpty()) {
      u = q.remove();
      var fact = constants.getInFact(u);

      // evaluate the expression and then check reachability based on branch restriction
      if (u instanceof If) {
        var cond = ((If) u).getCondition();
        var res = evaluate(cond, fact);
        for (var e : cfg.getOutEdgesOf(u)) {
          if (!reachable_if(res, e))
            continue;
          handle_edge(q, vis, e);
        }
      } else if (u instanceof SwitchStmt) {
        // need to consider case and default target
        Value res = fact.get(((SwitchStmt) u).getVar());
        if (!res.isConstant()) {
          for (var e : cfg.getOutEdgesOf(u)) {
            handle_edge(q, vis, e);
          }
        } else {
          boolean has_default = false;
          boolean hit = false;
          // handle switch case first
          for (var e : cfg.getOutEdgesOf(u)) {
            if (e.getKind() == Kind.SWITCH_DEFAULT) {
              has_default = true;
              continue;
            }
            if (!reachable_switch_case(res, e))
              continue;
            hit = true;
            handle_edge(q, vis, e);
          }
          if (has_default && !hit) {
            var t = ((SwitchStmt) u).getDefaultTarget();
            handle_node(q, vis, t);
          }
        }
      } else
        for (Stmt v : cfg.getSuccsOf(u)) {
          handle_node(q, vis, v);
        }
    }

    return vis;
  }

  @Override
  public Set<Stmt> analyze(IR ir) {
    // obtain CFG
    CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
    // obtain result of constant propagation
    DataflowResult<Stmt, CPFact> constants = ir.getResult(ConstantPropagation.ID);
    // obtain result of live variable analysis
    DataflowResult<Stmt, SetFact<Var>> liveVars = ir.getResult(LiveVariableAnalysis.ID);
    // keep statements (dead code) sorted in the resulting set
    Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
    // Your task is to recognize dead code in ir and add it to deadCode

    // add useless Assignment code
    for (Stmt stmt : cfg) {
      if (!(stmt instanceof AssignStmt))
        continue;

      if (has_side_effect(stmt))
        continue;

      // check for usage
      if (useless(stmt, liveVars))
        deadCode.add(stmt);
    }

    Set<Stmt> reachable = get_reachable(cfg, constants);
    for (Stmt stmt : cfg) {
      if (cfg.isExit(stmt)) {
        continue;
      }
      if (reachable.contains(stmt))
        continue;
      deadCode.add(stmt);
    }
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
