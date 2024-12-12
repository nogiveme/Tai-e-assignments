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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me
    public void processSource(CSCallSite csCallSite, CSVar recv) {
        Invoke callSite = csCallSite.getCallSite();
        Set<Source> sources = config.getSources();
        JMethod method = callSite.getMethodRef().resolve();
        Type type = method.getReturnType();
        if (sources.contains(new Source(method, type))) {
            solver.addTaintEdge(null, recv, manager.makeTaint(callSite, type));
        }
    }

    public void processTaintTransfer(CSCallSite csCallSite, CSVar base) {
        PointerAnalysisResult result = solver.getResult();
        CallGraph<CSCallSite, CSMethod> csCallGraph = result.getCSCallGraph();
        csCallGraph.edges().forEach(edge -> {
            if (edge.getCallSite().equals(csCallSite)) {
                JMethod method = edge.getCallee().getMethod();
                Type type = method.getReturnType();
                Context context = csCallSite.getContext();
                CSVar csRet = null;
                if (csCallSite.getCallSite().getLValue() != null) {
                    csRet = csManager.getCSVar(context, csCallSite.getCallSite().getLValue());
                }
                processBaseToResult(method, type, base, csRet);
                processArgToResult(method, type, csRet, csCallSite);
                processArgToBase(method, type, base, csCallSite);
            }
        });
    }


    private void processBaseToResult(JMethod method, Type type, CSVar base, CSVar ret) {
        if (base == null || ret == null) return ;
        TaintTransfer taintTransfer = new TaintTransfer(method, TaintTransfer.BASE, TaintTransfer.RESULT, type);
        if (config.getTransfers().contains(taintTransfer)) {
            base.getPointsToSet().forEach(csObj -> {
                if (manager.isTaint(csObj.getObject())) {
                    Invoke source = manager.getSourceCall(csObj.getObject());
                    solver.addTaintEdge(
                            base,
                            ret,
                            manager.makeTaint(source, type)
                    );
                }
            });
        }
    }

    private void processArgToBase(JMethod method, Type type, CSVar base, CSCallSite csCallSite) {
        if (base == null) return;
        PointerAnalysisResult result = solver.getResult();
        for (int index = 0; index < method.getParamCount(); index++) {
            Var arg = csCallSite.getCallSite().getInvokeExp().getArg(index);
            for (Obj obj: result.getPointsToSet(arg)) {
                if (manager.isTaint(obj)) {
                    TaintTransfer taintTransfer = new TaintTransfer(method, index, TaintTransfer.BASE, type);
                    if (config.getTransfers().contains(taintTransfer)) {
                        Invoke source = manager.getSourceCall(obj);
                        solver.addTaintEdge(
                                csManager.getCSVar(csCallSite.getContext(), arg),
                                base,
                                manager.makeTaint(source, type)
                        );
                    }
                }
            }
        }
    }

    private void processArgToResult(JMethod method, Type type, CSVar ret, CSCallSite csCallSite) {
        if (ret == null) return;
        PointerAnalysisResult result = solver.getResult();
        for (int index = 0; index < method.getParamCount(); index++) {
            Var arg = csCallSite.getCallSite().getInvokeExp().getArg(index);
            for (Obj obj : result.getPointsToSet(arg)) {
                if (manager.isTaint(obj)) {
                    TaintTransfer taintTransfer = new TaintTransfer(method, index, TaintTransfer.RESULT, type);
                    if (config.getTransfers().contains(taintTransfer)) {
                        Invoke source = manager.getSourceCall(obj);
                        solver.addTaintEdge(
                                csManager.getCSVar(csCallSite.getContext(), arg),
                                ret,
                                manager.makeTaint(source, type)
                        );
                    }
                }
            }
        }
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        //TODO
        result.getCSCallGraph().edges().forEach(edge -> {
            JMethod method = edge.getCallee().getMethod();
            for (int index = 0; index < method.getParamCount(); index++) {
                Sink sink = new Sink(method, index);
                if (config.getSinks().contains(sink)) {
                    Var arg = edge.getCallSite().getCallSite().getInvokeExp().getArg(index);
                    for (var obj : result.getPointsToSet(arg)) {
                        if (manager.isTaint(obj)) {
                            taintFlows.add(new TaintFlow(
                                    manager.getSourceCall(obj),
                                    edge.getCallSite().getCallSite(),
                                    index
                            ));
                        }
                    }
                }
            }
        });
        return taintFlows;
    }
}
