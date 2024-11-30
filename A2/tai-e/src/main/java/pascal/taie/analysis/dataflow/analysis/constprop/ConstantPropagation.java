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
 * ANY WARRANTY; without even the implied warrant of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

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
        // TODO - finish me
        var fact = new CPFact();
        cfg.getIR().getParams().forEach(param -> {
            if (canHoldInt(param))
                fact.update(param, Value.getNAC());
        });
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (var key : fact.keySet()) {
            var value1 = fact.get(key);
            var value2 = target.get(key);
            target.update(key, meetValue(value1, value2));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        if (v1.isUndef()  && v2.isUndef()) return Value.getUndef();
        if (v1.isUndef() || v2.isUndef()) return v1.isConstant() ?
                Value.makeConstant(v1.getConstant()) : Value.makeConstant(v2.getConstant());
        return v1.getConstant() == v2.getConstant() ?
                Value.makeConstant(v1.getConstant()) : Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // make sure def can hold int
        var oldOut = out.copy();
        out.clear(); out.copyFrom(in);
        if (stmt instanceof DefinitionStmt<?,?>) {
            var lv = ((DefinitionStmt<?, ?>) stmt).getLValue();
            var rv = ((DefinitionStmt<?, ?>) stmt).getRValue();
            if (!(lv instanceof Var) || !canHoldInt((Var) lv)) return false;
            out.remove((Var) lv);
            out.update((Var) lv, evaluate(rv, in));
        }
        return !oldOut.equals(out);
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
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var) {
            return in.get((Var) exp).isConstant() ?
                    Value.makeConstant(in.get((Var)exp).getConstant()) : in.get((Var)exp);
        }
        if (exp instanceof IntLiteral) return Value.makeConstant(((IntLiteral) exp).getValue());
        if (!(exp instanceof BinaryExp)) return Value.getNAC();
        var o1 = evaluate(((BinaryExp) exp).getOperand1(), in);
        var o2 = evaluate(((BinaryExp) exp).getOperand2(), in);
        if (o1.isNAC() || o2.isNAC()) return Value.getNAC();
        else if (o1.isConstant() && o2.isConstant()) {
            if (exp instanceof BitwiseExp) {
                var op = ((BitwiseExp) exp).getOperator();
                switch (op) {
                    case OR -> {
                        return Value.makeConstant(o1.getConstant() | o2.getConstant());
                    }
                    case XOR -> {
                        return Value.makeConstant(o1.getConstant() ^ o2.getConstant());
                    }
                    case AND -> {
                        return Value.makeConstant(o1.getConstant() & o2.getConstant());
                    }
                }
            }
            if (exp instanceof ArithmeticExp) {
                var op = ((ArithmeticExp) exp).getOperator();
                switch (op) {
                    case ADD -> {
                        return Value.makeConstant(o1.getConstant() + o2.getConstant());
                    }
                    case SUB -> {
                        return Value.makeConstant(o1.getConstant() - o2.getConstant());
                    }
                    case MUL -> {
                        return Value.makeConstant(o1.getConstant() * o2.getConstant());
                    }
                    case DIV -> {
                        if (o2.getConstant() == 0) return Value.getUndef();
                        return Value.makeConstant(o1.getConstant() / o2.getConstant());
                    }
                    case REM -> {
                        if (o2.getConstant() == 0) return Value.getUndef();
                        return Value.makeConstant(o1.getConstant() % o2.getConstant());
                    }
                }
            }
            if (exp instanceof ConditionExp) {
                var op = ((ConditionExp) exp).getOperator();
                switch (op) {
                    case EQ -> {
                        return Value.makeConstant(o1.getConstant() == o2.getConstant() ? 1 : 0);
                    }
                    case GE -> {
                        return Value.makeConstant(o1.getConstant() >= o2.getConstant() ? 1 : 0);
                    }
                    case GT -> {
                        return Value.makeConstant(o1.getConstant() > o2.getConstant() ? 1 : 0);
                    }
                    case LE -> {
                        return Value.makeConstant(o1.getConstant() <= o2.getConstant() ? 1 : 0);
                    }
                    case LT -> {
                        return Value.makeConstant(o1.getConstant() < o2.getConstant() ? 1 : 0);
                    }
                }
            }
            if (exp instanceof ShiftExp) {
                var op = ((ShiftExp) exp).getOperator();
                switch (op) {
                    case SHL -> {
                        return Value.makeConstant(o1.getConstant() << o2.getConstant());
                    }
                    case SHR -> {
                        return Value.makeConstant(o1.getConstant() >> o2.getConstant());
                    }
                    case USHR -> {
                        return Value.makeConstant(o1.getConstant() >>> o2.getConstant());
                    }
                }
            }
        }
        return Value.getUndef();
    }
}
