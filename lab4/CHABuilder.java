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
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

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
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        // Initialize
        Queue<JMethod> working_list = new LinkedList<>();
        working_list.add(entry);

        while (!working_list.isEmpty()) {
            var m = working_list.poll();
            if (!callGraph.contains(m)) {
                callGraph.addReachableMethod(m);

                callGraph.callSitesIn(m).forEach(call_site -> {
                    resolve(call_site).forEach(m_ -> {
                        if (call_site.isStatic()) {
                            callGraph.addEdge(new Edge<>(CallKind.STATIC, call_site, m_));
                            working_list.add(m_);
                        }
                        if (call_site.isSpecial()) {
                            callGraph.addEdge(new Edge<>(CallKind.SPECIAL, call_site, m_));
                            working_list.add(m_);
                        }
                        if (call_site.isInterface()) {
                            callGraph.addEdge(new Edge<>(CallKind.INTERFACE, call_site, m_));
                            working_list.add(m_);
                        }
                        if (call_site.isVirtual()) {
                            callGraph.addEdge(new Edge<>(CallKind.VIRTUAL, call_site, m_));
                            working_list.add(m_);
                        }
                    });

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
        var T = new HashSet<JMethod>();
        var cs = CallGraphs.getCallKind(callSite);
        var m = callSite.getMethodRef();

        switch (cs) {
            case INTERFACE:
            case VIRTUAL: {
                // foreach 𝑐′ that is a subclass of 𝑐 or 𝑐 itself do
                //add Dispatch(𝑐′, 𝑚𝑚) to T
                Queue<JClass> subclasses_list = new LinkedList<>();
                subclasses_list.add(m.getDeclaringClass());

                while (!subclasses_list.isEmpty()) {
                    var c = subclasses_list.poll();

                    var t = dispatch(c, m.getSubsignature());
                    if (t != null) {
                        T.add(t);
                    }

                    if (c.isInterface()) {
                        subclasses_list.addAll(this.hierarchy.getDirectImplementorsOf(c));
                        subclasses_list.addAll(this.hierarchy.getDirectSubinterfacesOf(c));
                    }
                    else {
                        subclasses_list.addAll(this.hierarchy.getDirectSubclassesOf(c));
                    }
                }
            }
            case SPECIAL: {
                var cm = m.getDeclaringClass();
                var t = dispatch(cm, m.getSubsignature());
                if (t != null) {
                    T.add(t);
                }
                break;
            }
            case STATIC: {
                T.add(m.getDeclaringClass().getDeclaredMethod(m.getSubsignature()));
                break;
            }
            default: ;
        }

        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        var m = jclass.getDeclaredMethod(subsignature);

        // If jclass contains non-abstract method m that
        // has the same name and descriptor as subsignature,
        // then return m.
        if (m != null && !m.isAbstract()) {
            return m;
        }

        // Otherwise do `dispatch(j, subsignature)` where j is super class of jclass.
        var super_class = jclass.getSuperClass();
        if (super_class != null) {
            return dispatch(jclass.getSuperClass(), subsignature);
        }

        return null;
    }
}