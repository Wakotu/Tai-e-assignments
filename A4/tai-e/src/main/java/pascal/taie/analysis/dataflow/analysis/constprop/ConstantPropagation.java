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
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

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
      // need to judge if `par` is int
      if (!canHoldInt(par))
        continue;
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

  private static boolean merge(CPFact fact, CPFact target) {
    var flag = false;
    for (var key : fact.keySet()) {
      flag = flag | target.update(key, fact.get(key));
    }
    return flag;
  }

  @Override
  // returns whether the out(in) Node has changed
  public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
    var temp = out.copy();
    var flag = merge(in, out);

    Var def = null;
    try {
      var x = stmt.getDef().get();
      if (x instanceof Var)
        def = (Var) x;
    } catch (NoSuchElementException e) {
    }

    if (def == null)
      return flag;

    // didn't care about no int variables
    if (!canHoldInt(def))
      return flag;
    if (def.getStoreFields().size() > 0)
      return flag;

    var useList = stmt.getUses();
    // check `%this` to detect method call
    // for (var use : useList) {
    //   if (use instanceof Var) {
    //     Var x = (Var) use;
    //     if (x.getName().equals("%this")) {
    //       flag |= out.update(def, Value.getNAC());
    //       return flag;
    //     }
    //   }
    // }

    // check method call
    if (stmt instanceof Invoke) {
      out.update(def, Value.getNAC());
      return out.equals(temp);
    }
    // check load Fields to detect object fileds
    for (var use : useList) {
      if (use instanceof Var) {
        Var x = (Var) use;
        if (x.getLoadFields().size() > 0) {
          out.update(def, Value.getNAC());
          return out.equals(temp);
        }
      }
    }
    if (useList.size() == 1 || useList.size() == 3) {
      var val = evaluate(useList.get(useList.size() - 1), in);
      if (val != null) {
        out.update(def, val);
        return out.equals(temp);
      }
    }
    return flag;
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

  private static Value calc(int a, int b, ArithmeticExp exp) {
    var op = exp.getOperator();
    Value res = null;
    switch (op) {
      case ADD:
        res = Value.makeConstant(a + b);
        break;
      case SUB:
        res = Value.makeConstant(a - b);
        break;
      case MUL:
        res = Value.makeConstant(a * b);
        break;
      case DIV:
        if (b == 0) {
          res = Value.getNAC();
        } else {
          res = Value.makeConstant(a / b);
        }
        break;
      case REM:
        if (b == 0) {
          res = Value.getNAC();
        } else {
          res = Value.makeConstant(a % b);
        }
        break;

      default:
        break;
    }
    return res;
  }

  private static Value calc(int a, int b, ConditionExp exp) {
    var op = exp.getOperator();
    Value res = null;
    switch (op) {
      case EQ:
        res = Value.makeConstant(a == b ? 1 : 0);
        break;
      case NE:
        res = Value.makeConstant(a != b ? 1 : 0);
        break;
      case LT:
        res = Value.makeConstant(a < b ? 1 : 0);
        break;
      case GT:
        res = Value.makeConstant(a > b ? 1 : 0);
        break;
      case LE:
        res = Value.makeConstant(a <= b ? 1 : 0);
        break;
      case GE:
        res = Value.makeConstant(a >= b ? 1 : 0);
        break;

      default:
        break;
    }
    return res;
  }

  private static Value calc(int a, int b, BitwiseExp exp) {
    var op = exp.getOperator();
    Value res = null;
    switch (op) {
      case OR:
        res = Value.makeConstant(a | b);
        break;
      case AND:
        res = Value.makeConstant(a & b);
        break;
      case XOR:
        res = Value.makeConstant(a ^ b);
        break;
      default:
        break;
    }
    return res;
  }

  private static Value calc(int a, int b, ShiftExp exp) {
    var op = exp.getOperator();
    Value res = null;
    switch (op) {
      case SHL:
        res = Value.makeConstant(a << b);
        break;
      case SHR:
        res = Value.makeConstant(a >> b);
        break;
      case USHR:
        res = Value.makeConstant(a >>> b);
        break;

      default:
        break;
    }
    return res;
  }

  private static Value calculate(int a, int b, BinaryExp bexp) {
    if (bexp instanceof ArithmeticExp) {
      return calc(a, b, (ArithmeticExp) bexp);
    }
    if (bexp instanceof ConditionExp) {
      return calc(a, b, (ConditionExp) bexp);
    }
    if (bexp instanceof BitwiseExp) {
      return calc(a, b, (BitwiseExp) bexp);
    }
    if (bexp instanceof ShiftExp) {
      return calc(a, b, (ShiftExp) bexp);
    }
    return null;
  }

  /**
   * Evaluates the {@link Value} of given expression.
   *
   * @param exp the expression to be evaluated
   * @param in  IN fact of the statement
   * @return the resulting {@link Value}
   */
  public static Value evaluate(Exp exp, CPFact in) {
    // judge the type of expression
    if (exp instanceof Var)
      return in.get((Var) exp);
    if (exp instanceof IntLiteral) {
      int x = ((IntLiteral) exp).getValue();
      return Value.makeConstant(x);
    }
    if (exp instanceof BinaryExp) {
      var bexp = (BinaryExp) exp;
      Var v1 = bexp.getOperand1(), v2 = bexp.getOperand2();
      if (in.get(v1).isNAC() || in.get(v2).isNAC())
        return Value.getNAC();
      if (in.get(v1).isUndef() || in.get(v2).isUndef())
        return Value.getUndef();

      return calculate(in.get(v1).getConstant(), in.get(v2).getConstant(), bexp);
    }
    return null;
  }
}
