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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.util.collection.SetQueue;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    public void addTask(Node node) {
        workList.offer(node);
    }

    private void initialize() {
        // TODO - finish me
        workList = new LinkedList<>(icfg.getNodes());
        for (var node : icfg.getNodes()) {
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        }
        icfg.entryMethods().forEach(method -> {
            Node entry = icfg.getEntryOf(method);
            result.setOutFact(entry, analysis.newBoundaryFact(entry));
        });
    }

    private void doSolve() {
        // TODO - finish me
        if (!(analysis instanceof InterConstantPropagation constantAnalysis)) return;
        while (!workList.isEmpty()) {
            Node node = workList.poll();
            CPFact in = (CPFact) result.getInFact(node);
            icfg.getInEdgesOf(node).forEach(edge -> {
                constantAnalysis.meetInto(
                        (CPFact) analysis.transferEdge(edge, result.getOutFact(edge.getSource())),
                        in);
            });
            constantAnalysis.processStoreField((Stmt) node, in);
            constantAnalysis.processStoreArray((Stmt) node, in);
            if(analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                icfg.getSuccsOf(node).forEach(workList::offer);
            }
        }
    }
}
