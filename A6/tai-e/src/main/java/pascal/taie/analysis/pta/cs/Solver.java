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

package pascal.taie.analysis.pta.cs;

import fj.P;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        // csManager manage nodes and cs element
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    private void analyze() {
        while (!workList.isEmpty()) {
            // pick top task and propagate
            var entry = workList.pollEntry();
            var pointer = entry.pointer();
            var pts = entry.pointsToSet();
            var delta = propagate(pointer, pts);

            // if pointer is var then process it
            if (!(pointer instanceof  CSVar)) continue;
            var var = ((CSVar) pointer).getVar();
            var context = ((CSVar) pointer).getContext();
            for (var csobj: delta) {
                for (var loadField : var.getLoadFields()) {
                    addPFGEdge(
                            csManager.getInstanceField(csobj, loadField.getFieldAccess().getFieldRef().resolve()),
                            csManager.getCSVar(context, loadField.getLValue())
                    );
                }
                for (var storeField : var.getStoreFields()) {
                    addPFGEdge(
                            csManager.getCSVar(context, storeField.getRValue()),
                            csManager.getInstanceField(csobj, storeField.getFieldAccess().getFieldRef().resolve())
                    );
                }
                for (var loadArrayField : var.getLoadArrays()) {
                    addPFGEdge(
                            csManager.getArrayIndex(csobj),
                            csManager.getCSVar(context, loadArrayField.getLValue())
                    );
                }
                for (var storeArrayField : var.getStoreArrays()) {
                    addPFGEdge(
                            csManager.getCSVar(context, storeArrayField.getRValue()),
                            csManager.getArrayIndex(csobj)
                    );
                }
                processCall((CSVar)pointer, csobj);
            }
        }
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // add method which have not been visited
        if (callGraph.contains(csMethod)) {
            return;
        }
        callGraph.addReachableMethod(csMethod);

        // process statements in new method, e.g. new and copy
        var processor = new StmtProcessor(csMethod);
        csMethod.getMethod().getIR().getStmts().forEach(stmt -> {
            stmt.accept(processor);
        });
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }


        @Override
        public Void visit(Invoke stmt) {
            if (!stmt.isStatic()) {
                return null;
            }
            JMethod method = resolveCallee(null, stmt);
            CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
            Context ct = contextSelector.selectContext(csCallSite, method);
            CSMethod tarMethod = csManager.getCSMethod(ct, method);
            if (callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, tarMethod))) {
                addReachable(tarMethod);
                for (int i = 0; i < method.getParamCount(); i++) {
                    CSVar param = csManager.getCSVar(context, stmt.getRValue().getArg(i));
                    CSVar ref = csManager.getCSVar(context, method.getIR().getParam(i));
                    addPFGEdge(param, ref);
                }
                if (stmt.getLValue() != null) {
                    CSVar rec = csManager.getCSVar(context, stmt.getLValue());
                    for (Var ret : method.getIR().getReturnVars()) {
                        CSVar retVar = csManager.getCSVar(ct, ret);
                        addPFGEdge(retVar, rec);
                    }
                }
            }
            return null;
        }

        @Override
        public Void visit(New stmt) {
            CSVar csVar = csManager.getCSVar(context, stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            var csObj = csManager.getCSObj(heapContext, obj);
            var pts = PointsToSetFactory.make(csObj);
            workList.addEntry(csVar, pts);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            var rightVal = csManager.getCSVar(context, stmt.getRValue());
            var leftVal = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(rightVal, leftVal);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (!stmt.isStatic()) {
                return null;
            }
            var csVar = csManager.getCSVar(context, stmt.getRValue());
            var field = stmt.getFieldRef().resolve();
            var staticField = csManager.getStaticField(field);
            addPFGEdge(csVar, staticField);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (!stmt.isStatic()) {
                return null;
            }
            var csVar = csManager.getCSVar(context, stmt.getLValue());
            var field = stmt.getFieldRef().resolve();
            var staticField = csManager.getStaticField(field);
            addPFGEdge(staticField, csVar);
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.getSuccsOf(source).contains(target)) return ;
        if (pointerFlowGraph.addEdge(source, target)
                && !source.getPointsToSet().isEmpty()) {
            workList.addEntry(target, source.getPointsToSet());
        }
    }


    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var delta = PointsToSetFactory.make();
        pointsToSet.objects()
                .filter(csObj -> !pointer.getPointsToSet().contains(csObj))
                .forEach(delta::addObject);
        if (!delta.isEmpty()) {
            pointer.getPointsToSet().addAll(delta);
            pointerFlowGraph.getSuccsOf(pointer).forEach(suc -> {
                workList.addEntry(suc, delta);
            });
        }
        return delta;
    }

    /**
     * Processes instance calls when p
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        Var var = recv.getVar();
        for (var invoke : var.getInvokes()) {
            // Generate context for target method
            JMethod method = resolveCallee(recvObj, invoke);
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), invoke);
            Context ct = contextSelector.selectContext(csCallSite, recvObj, method);

            // Get this pointer of context method
            CSMethod targetMethod = csManager.getCSMethod(ct, method);
            CSVar thisPointer = csManager.getCSVar(ct, method.getIR().getThis());

            // Transfer recvObj to this pointer
            workList.addEntry(thisPointer, PointsToSetFactory.make(recvObj));
            Edge<CSCallSite, CSMethod> edge = getCsCallSiteCSMethodEdge(invoke, csCallSite, targetMethod);
            if (callGraph.addEdge(edge)) {
                addReachable(targetMethod);
                // add edges from actual params to ref params
                for (int i = 0; i < method.getParamCount(); i++) {
                    CSVar param = csManager.getCSVar(recv.getContext(), invoke.getRValue().getArg(i));
                    CSVar ref = csManager.getCSVar(ct, method.getIR().getParam(i));
                    addPFGEdge(param, ref);
                }
                if (invoke.getLValue() != null) {
                    CSVar rec = csManager.getCSVar(recv.getContext(), invoke.getLValue());
                    for (Var ret : method.getIR().getReturnVars()) {
                        CSVar retVar = csManager.getCSVar(ct, ret);
                        addPFGEdge(retVar, rec);
                    }
                }
            }
        }
    }

    private static Edge<CSCallSite, CSMethod> getCsCallSiteCSMethodEdge(Invoke invoke, CSCallSite csCallSite, CSMethod tarMethod) {
        Edge<CSCallSite, CSMethod> edge = null;
        if (invoke.isDynamic()) {
            edge = new Edge<>(CallKind.DYNAMIC, csCallSite, tarMethod);
        } else if (invoke.isVirtual()) {
            edge = new Edge<>(CallKind.VIRTUAL, csCallSite, tarMethod);
        } else if (invoke.isSpecial()) {
            edge = new Edge<>(CallKind.SPECIAL, csCallSite, tarMethod);
        } else if (invoke.isInterface()) {
            edge = new Edge<>(CallKind.INTERFACE, csCallSite, tarMethod);
        }
        return edge;
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
