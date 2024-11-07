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

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import polyglot.util.WorkList;

import java.lang.invoke.CallSite;
import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

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
        DefaultCallGraph callGraph = new DefaultCallGraph();
//        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> worklist = new ArrayDeque<>();
        worklist.add(entry);
        while (!worklist.isEmpty()) {
            JMethod method = worklist.remove();
            if (!callGraph.contains(method)) {
                callGraph.addReachableMethod(method);
                callGraph.callSitesIn(method).forEach(cs -> {
                    var methods = resolve(cs);
                    for (var m : methods) {
                        var edge = new Edge<Invoke, JMethod>(CallGraphs.getCallKind(cs), cs, m);
                        callGraph.addEdge(edge);
                        worklist.add(m);
                    }
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> candidates = new HashSet<>();
        var kind = CallGraphs.getCallKind(callSite);
        var methodRef = callSite.getMethodRef();
        var declareClass = methodRef.getDeclaringClass();
        var signature = methodRef.getSubsignature();
        if (kind == CallKind.STATIC) {
            var method = declareClass.getDeclaredMethod(signature);
            candidates.add(method);
            return candidates;
        }
        if (kind == CallKind.SPECIAL) {
            candidates.add(dispatch(declareClass, signature));
            return candidates;
        }
        if (kind == CallKind.VIRTUAL) {
            candidates.add(dispatch(declareClass, signature));
            hierarchy.getDirectSubclassesOf(declareClass).forEach(jClass -> {
                candidates.add(dispatch(jClass, methodRef.getSubsignature()));
            });
        }
        return candidates;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        var method = jclass.getDeclaredMethod(subsignature);
        if (method != null) return method;
        if (jclass.getSuperClass() == null) return null;
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
