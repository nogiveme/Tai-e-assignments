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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Pair;

import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private HashMap<Obj, Set<Var>> aliasCollection;

    private HashMap<Pair<?, ?>, Value> fields;

    private HashMap<Pair<JClass, FieldRef>, Set<LoadField>> staticLoadFields;

    private PointerAnalysisResult pta;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
        aliasCollection = new HashMap<>();
        fields = new HashMap<>();
        staticLoadFields = new HashMap<>();
        for (var obj : pta.getObjects()) {
            for (Var var : pta.getVars()) {
                if (pta.getPointsToSet(var).contains(obj)) {
                    Set<Var> vars = aliasCollection.getOrDefault(obj, new HashSet<>());
                    vars.add(var);
                    aliasCollection.put(obj, vars);
                }
            }
        }
        for (var stmt : icfg) {
            if (stmt instanceof LoadField loadField
            && loadField.getFieldAccess() instanceof StaticFieldAccess staticFieldAccess) {
                Pair<JClass, FieldRef> field = new Pair<>(staticFieldAccess.getFieldRef().getDeclaringClass(),
                        staticFieldAccess.getFieldRef());
                Set<LoadField> set = staticLoadFields.getOrDefault(field, new HashSet<>());
                set.add(loadField);
                staticLoadFields.put(field, set);
            }
        }
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
        // TODO - finish me
        AtomicBoolean changed = new AtomicBoolean(false);
        in.forEach(((var, value) -> {
            if(out.update(var, value)){
                changed.set(true);
            }
        }));
        return changed.get();
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt instanceof LoadField loadField) {
            boolean changed = basicCheck(in, out);
            if (!ConstantPropagation.canHoldInt(loadField.getLValue())) return changed;
            CPFact inCopy = in.copy();
            Value removedVal = inCopy.get(loadField.getLValue());
            inCopy.remove(loadField.getLValue());
            if (loadField.getFieldAccess() instanceof StaticFieldAccess staticFieldAccess) {
                Value value = fields.getOrDefault(
                        new Pair<>(staticFieldAccess.getFieldRef().getDeclaringClass(), staticFieldAccess.getFieldRef()),
                        Value.getUndef()
                );
                out.update(loadField.getLValue(), value);
                return changed || !value.equals(removedVal);
            }
            if (loadField.getFieldAccess() instanceof InstanceFieldAccess instanceFieldAccess) {
                Value value = Value.getUndef();
                for (Obj obj : pta.getPointsToSet(instanceFieldAccess.getBase())) {
                    value = cp.meetValue(
                            value,
                            fields.getOrDefault(new Pair<>(obj, instanceFieldAccess.getFieldRef()), Value.getUndef())
                    );
                }
                out.update(loadField.getLValue(), value);
                return changed || !value.equals(removedVal);
            }
        } else if (stmt instanceof LoadArray loadArray) {
            boolean changed = basicCheck(in, out);
            if (!ConstantPropagation.canHoldInt(loadArray.getLValue())) return changed;
            CPFact inCopy = in.copy();
            Value removedValue = inCopy.get(loadArray.getLValue());
            inCopy.remove(loadArray.getLValue());

            Var index = loadArray.getArrayAccess().getIndex();
            Value indexValue = ConstantPropagation.evaluate(index, in);
            Value value = Value.getUndef();

            if (indexValue.isConstant()) {
                for (Obj obj : pta.getPointsToSet(loadArray.getArrayAccess().getBase())){
                    value = cp.meetValue(value, fields.getOrDefault(new Pair<>(obj, indexValue), Value.getUndef()));
                    value = cp.meetValue(value, fields.getOrDefault(new Pair<>(obj, Value.getNAC()), Value.getUndef()));
                }
            }
            if (indexValue.isNAC()) {
                for(Obj obj : pta.getPointsToSet(loadArray.getArrayAccess().getBase())){
                    for(Map.Entry<Pair<?, ?>, Value> entry : fields.entrySet()){
                        Pair<?, ?> accessPair = entry.getKey();
                        if(accessPair.first().equals(obj) && accessPair.second() instanceof Value){
                            value = cp.meetValue(value, entry.getValue());
                        }
                    }
                }
            }
            out.update(loadArray.getLValue(), value);
            return changed || !value.equals(removedValue);
        }
        return cp.transferNode(stmt, in, out);
    }

    private boolean basicCheck(CPFact in, CPFact out) {
        AtomicBoolean changed = new AtomicBoolean(false);
        in.forEach(((var, value) -> {
            if(out.update(var, value)){
                changed.set(true);
            }
        }));
        return changed.get();
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact out_trans = out.copy();
        Stmt source = edge.getSource();
        source.getDef().ifPresent(lValue -> {
            if (lValue instanceof Var var) {
                out_trans.remove(var);
            }
        });
        return out_trans;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        Invoke invoke = (Invoke) edge.getSource();
        CPFact res = new CPFact();
        List<Var> params = edge.getCallee().getIR().getParams();
        List<Var> args = invoke.getRValue().getArgs();
        assert args.size() == params.size();
        for (int i = 0; i < params.size(); i++) {
            res.update(params.get(i), callSiteOut.get(args.get(i)));
        }
        return res;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact res = new CPFact();
        Collection<Var> returnVars = edge.getReturnVars();
        edge.getCallSite().getDef().ifPresent(lValue -> {
            if (lValue instanceof Var var) {
                returnVars.forEach(returnVar -> {
                    res.update(var, cp.meetValue(res.get(var), returnOut.get(returnVar)));
                });
            }
        });
        return res;
    }

    protected void processStoreField(Stmt stmt, CPFact in) {
        if (!(stmt instanceof StoreField storeField)) return;
        if (storeField.getFieldAccess() instanceof StaticFieldAccess staticFieldAccess) {
            FieldRef fieldRef = staticFieldAccess.getFieldRef();
            JClass declaringClass = fieldRef.getDeclaringClass();
            Value rightValue = ConstantPropagation.evaluate(storeField.getRValue(), in);
            Value fieldValue = fields.getOrDefault(new Pair<>(declaringClass, fieldRef), Value.getUndef());
            Value meetValue = cp.meetValue(fieldValue, rightValue);
            if (!meetValue.equals(fieldValue)) {
                fields.put(new Pair<>(declaringClass, fieldRef), meetValue);
                staticLoadFields.getOrDefault(new Pair<>(declaringClass, fieldRef), new HashSet<>())
                        .forEach(loadField -> {
                            solver.addTask(loadField);
                        });
            }
        }
        if (storeField.getFieldAccess() instanceof InstanceFieldAccess instanceFieldAccess) {
            Var base = instanceFieldAccess.getBase();
            FieldRef field = instanceFieldAccess.getFieldRef();
            Value rightValue = ConstantPropagation.evaluate(storeField.getRValue(), in);
            for (Obj obj : pta.getPointsToSet(base)) {
                Value fieldValue = fields.getOrDefault(new Pair<>(obj, field), Value.getUndef());
                Value meetValue = cp.meetValue(fieldValue, rightValue);
                if (!meetValue.equals(fieldValue)) {
                    fields.put(new Pair<>(obj, field), meetValue);
                    aliasCollection.get(obj).forEach(alias -> {
                        alias.getLoadFields().forEach(loadField -> {
                            solver.addTask(loadField);
                        });
                    });
                }
            }
        }
    }

    protected void processStoreArray(Stmt stmt, CPFact in) {
        if (stmt instanceof StoreArray storeArray) {
            Var base = storeArray.getArrayAccess().getBase();
            Var index = storeArray.getArrayAccess().getIndex();
            Value indexValue = ConstantPropagation.evaluate(index, in);
            Value rightValue = ConstantPropagation.evaluate(storeArray.getRValue(), in);
            for (Obj obj : pta.getPointsToSet(base)) {
                Value fieldValue = fields.getOrDefault(new Pair<>(obj, indexValue), Value.getUndef());
                Value meetValue = cp.meetValue(fieldValue, rightValue);
                if (!meetValue.equals(fieldValue)) {
                    fields.put(new Pair<>(obj, indexValue), meetValue);
                    aliasCollection.get(obj).forEach(alias -> {
                        alias.getLoadArrays().forEach(loadArray -> {
                            solver.addTask(loadArray);
                        });
                    });
                }
            }
        }
    }
}
