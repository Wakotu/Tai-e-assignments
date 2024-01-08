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

import java.util.NoSuchElementException;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {
  public static final String ID = "inter-constprop";

  private final ConstantPropagation cp;

  public InterConstantPropagation(AnalysisConfig config) {
    super(config);
    cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
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
    // identity function with the ability to detect if modified
    var temp = out.copy();
    out.clear();
    for (var key : in.keySet()) {
      out.update(key, in.get(key));
    }
    return !out.equals(temp);
  }

  @Override
  protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
    return cp.transferNode(stmt, in, out);
  }

  @Override
  protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
    return out.copy();
  }

  private static Var extractDef(Stmt stmt) {
    Var def = null;
    try {
      var x = stmt.getDef().get();
      if (x instanceof Var)
        def = (Var) x;
    } catch (NoSuchElementException e) {
    }
    return def;
  }

  @Override
  protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
    var stmt = edge.getSource();
    Var x = extractDef(stmt);

    var res = out.copy();
    // handle res
    if (x != null) {
      res.remove(x);
    }

    return res;
  }

  @Override
  protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
    var cs = edge.getSource();
    // try to get value of real parameter
    var args = ((Invoke) cs).getInvokeExp().getArgs();
    var entry = edge.getTarget();
    // get formal parameter
    var ir = icfg.getContainingMethodOf(entry).getIR();
    var params = ir.getParams();
    // construct fact
    var fact = newInitialFact();
    assert args.size() == params.size() : "args length unequal to params";
    for (int i = 0; i < args.size(); i++) {
      var val = callSiteOut.get(args.get(i));
      fact.update(params.get(i), val);
    }
    return fact;
  }

  @Override
  protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
    var cs = edge.getCallSite();
    Var x = extractDef(cs);
    var fact = newInitialFact();
    if (x == null) {
      return fact;
    }
    var rets = edge.getReturnVars();
    // merge of multiple var here is equivalent to meet multiple values from multiple branch for one
    // var
    Value val = Value.getUndef();
    for (Var y : rets) {
      var t = returnOut.get(y);
      val = cp.meetValue(val, t);
    }
    fact.update(x, val);
    return fact;
  }
}
