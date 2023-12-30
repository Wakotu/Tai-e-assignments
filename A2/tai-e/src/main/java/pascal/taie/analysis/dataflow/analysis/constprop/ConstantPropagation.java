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

import java.util.NoSuchElementException;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends AbstractDataflowAnalysis<Stmt, CPFact> {
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
    var fact = new CPFact();
    // initialize each paramter as NAC
    for (var par : cfg.getIR().getParams()) {
      fact.update(par, Value.getNAC());
    }
    return fact;
  }

  @Override
  public CPFact newInitialFact() {
    return new CPFact();
  }

  @Override
  public void meetInto(CPFact fact, CPFact target) {
    // merge fact into target
    for (var key : fact.keySet()) {
      var val1 = fact.get(key);
      var val2 = target.get(key); // UNDEF to represent the situation of miss
      var newVal = meetValue(val1, val2);
      target.update(key, newVal);
    }
  }

  /**
   * Meets two Values.
   */
  public Value meetValue(Value v1, Value v2) {
    if (v1.equals(v2))
      return v1;
    if (v1.isNAC() || v2.isNAC())
      return Value.getNAC();

    if (v1.isUndef())
      return v2;
    if (v2.isUndef())
      return v1;

    return Value.getNAC();
  }

  @Override
  // returns whether the out(in) Node has changed
  public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
    // TODO - finish me
    Var def = null;
    try {
      var x = stmt.getDef().get();
      if (x instanceof Var)
        def = (Var) x;
    } catch (NoSuchElementException e) {
    }

    if (def == null)
      return false;

    // didn't care about no int variables
    if (!canHoldInt(def))
      return false;

    out = in.copy();
    // get the right value

    return false;
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
        default:
          break;
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
    return null;
  }
}
