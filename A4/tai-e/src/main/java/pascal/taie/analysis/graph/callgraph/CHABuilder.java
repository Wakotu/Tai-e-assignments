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

package pascal.taie.analysis.graph.callgraph;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;
import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {
  private ClassHierarchy hierarchy;

  @Override
  public CallGraph<Invoke, JMethod> build() {
    hierarchy = World.get().getClassHierarchy();
    return buildCallGraph(World.get().getMainMethod());
  }

  private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
    // CG, reachable methods, queue
    DefaultCallGraph callGraph = new DefaultCallGraph();
    callGraph.addEntryMethod(entry);
    Queue<JMethod> q = new LinkedList<>();
    while (!q.isEmpty()) {
      JMethod u = q.remove();

      var csList = callGraph.callSitesIn(u).collect(Collectors.toList());
      for (var cs : csList) {
        var mSet = resolve(cs);
        for (var v : mSet) {
          callGraph.addEdge(new Edge<Invoke, JMethod>(CallGraphs.getCallKind(cs), cs, v));
          if (callGraph.contains(v))
            continue;
          callGraph.addReachableMethod(v);
          q.add(v);
        }
      }
    }
    return callGraph;
  }

  private void resolve_virtual(Set<JMethod> res, JClass c, Subsignature m) {
    // use CHA to
    if (c.isInterface()) {
      for (var sub : hierarchy.getDirectSubinterfacesOf(c)) {
        resolve_virtual(res, sub, m);
      }
      for (var sub : hierarchy.getDirectImplementorsOf(c)) {
        resolve_virtual(res, sub, m);
      }
    } else {
      // dispatch
      var t = dispatch(c, m);
      if (t != null)
        res.add(t);
      for (var sub : hierarchy.getDirectSubclassesOf(c)) {
        resolve_virtual(res, sub, m);
      }
    }
  }

  /**
   * Resolves call targets (callees) of a call site via CHA.
   */
  private Set<JMethod> resolve(Invoke callSite) {
    CallKind kind = CallGraphs.getCallKind(callSite);
    var ref = callSite.getMethodRef();
    JClass c = ref.getDeclaringClass();
    var m = ref.getSubsignature();
    Set<JMethod> res = new HashSet<>();
    switch (kind) {
      case STATIC:
        res.add(dispatch(c, m));
        break;

      case SPECIAL:
        res.add(dispatch(c, m));
        break;
      default:
        resolve_virtual(res, c, m);
        break;
    }
    return res;
  }

  /**
   * Looks up the target method based on given class and method subsignature.
   *
   * @return the dispatched target method, or null if no satisfying method
   * can be found.
   */
  private JMethod dispatch(JClass jclass, Subsignature subsignature) {
    JClass p = jclass;
    while (p != null) {
      JMethod m = p.getDeclaredMethod(subsignature);
      if (m != null && !m.isAbstract())
        return m;
      // p get upwards
      p = p.getSuperClass();
    }
    return null;
  }
}
