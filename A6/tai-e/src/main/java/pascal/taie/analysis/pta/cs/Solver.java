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

import java.lang.invoke.CallSite;

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
            var entry = workList.pollEntry();
            var pointer = entry.pointer();
            var pts = entry.pointsToSet();
            var delta = propagate(pointer, pts);
            if (pointer instanceof CSVar) {
                var ptn = pointer.getPointsToSet();
                var var = ((CSVar) pointer).getVar();
                var context = ((CSVar) pointer).getContext();
                for (var csobj : ptn) {
                    if (delta.contains(csobj)) continue;
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
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (!callGraph.contains(csMethod)) {
            callGraph.addEntryMethod(csMethod);
            csMethod.getMethod().getIR().getStmts().forEach(stmt -> {stmt.accept(new StmtProcessor(csMethod));});
        }
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


        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreArray stmt) {
            return StmtVisitor.super.visit(stmt);
        }


        @Override
        public Void visit(LoadArray stmt) {
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            return StmtVisitor.super.visit(stmt);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.getSuccsOf(source).contains(target)) return ;
        pointerFlowGraph.addEdge(source, target);
        workList.addEntry(target, source.getPointsToSet());
    }

    /**
     * Processes work-list entries until the work-list is emp
        // TODO - finish me
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        var delta = PointsToSetFactory.make();
        var cur_pts = pointer.getPointsToSet();
        for (var item : pointsToSet) {
            if (cur_pts.contains(item)) continue;
            delta.addObject(item);
            cur_pts.addObject(item);
        }
        pointer.setPointsToSet(cur_pts);
        for (var suc : pointerFlowGraph.getSuccsOf(pointer)) {
            workList.addEntry(suc, delta);
        }
        return delta;
    }

    /**
     * Processes instance calls when p
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        var var = recv.getVar();
        var context = recv.getContext();
        var invokes = var.getInvokes();
        for (var callsite : invokes) {
            var csCallsite = csManager.getCSCallSite(context, callsite);
            var callee = resolveCallee(recvObj, callsite);
            var calleeContext = contextSelector.selectContext(csCallsite, callee);
            var csCallee = csManager.getCSMethod(calleeContext, callee);
            workList.addEntry(
                    csManager.getCSVar(calleeContext, callee.getIR().getThis()),
                    PointsToSetFactory.make(recvObj)
            );
            if (callGraph.getCalleesOf(csCallsite).contains(csCallee)) continue;
            var callKind = getKind(callsite);
            callGraph.addEdge(new Edge<>(callKind, csCallsite, csCallee));
            addReachable(csCallee);
            var args = csCallee.getMethod().getIR().getParams();
//            assert args.size() == callsite.getRValue().getArgs().size();
            for(int i = 0;i < args.size();i ++){
                addPFGEdge(
                        csManager.getCSVar(context, callsite.getRValue().getArg(i)),
                        csManager.getCSVar(calleeContext, args.get(i))
                );
            }
            if(callsite.getLValue() != null){
                for (var ret : csCallee.getMethod().getIR().getReturnVars()) {
                    addPFGEdge(
                            csManager.getCSVar(calleeContext, ret),
                            csManager.getCSVar(context, callsite.getLValue())
                    );
                }
            }
        }
    }

    private CallKind getKind(Invoke invoke) {
        if (invoke.isInterface()) return CallKind.INTERFACE;
        if (invoke.isStatic()) return CallKind.STATIC;
        if (invoke.isSpecial()) return CallKind.SPECIAL;
        if (invoke.isVirtual()) return CallKind.VIRTUAL;
        return null;
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
