package net.sf.metacad.revenge.constraint;

import java.io.InputStream;

import alice.tuprolog.Int;
import alice.tuprolog.Prolog;
import alice.tuprolog.SolveInfo;
import alice.tuprolog.Struct;
import alice.tuprolog.Term;
import alice.tuprolog.Theory;
import alice.tuprolog.Var;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.arithmetic.ArithmeticVariableReference;
import net.sf.metacad.revenge.expression.arithmetic.BinaryArithmeticOperator;
import net.sf.metacad.revenge.expression.arithmetic.BinaryIntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.arithmetic.MinusIntegerExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonOperator;
import net.sf.metacad.revenge.type.NumericType;

public class PrologSimplifier {

	private static final String SOLUTION_PROLOG_VARIABLE_NAME = "Solution";

	public static CodeExpression solveEquation(CodeExpression codeExpression, String variableName) {
		CodeExpression value = null;
		try {
			InfixExpressionPrinter infixExpressionPrinter = new InfixExpressionPrinter();
			String infixExpression = infixExpressionPrinter.convert(codeExpression);
			// System.out.println("Prolog problem : " + infixExpression);
			Prolog engine = new Prolog();
			InputStream prologCode = PrologSimplifier.class.getResourceAsStream("arith.pl");
			if (prologCode == null) {
				throw new IllegalStateException(PrologSimplifier.class.getResource("arith.pl").toString());
			}
			Theory t = new Theory(prologCode);
			engine.setTheory(t);
			SolveInfo answer = engine.solve("equation_solution(" + infixExpression + "," + variableName + ","
					+ SOLUTION_PROLOG_VARIABLE_NAME + ").");
			if (answer.isSuccess()) {
				Term solution = answer.getTerm(SOLUTION_PROLOG_VARIABLE_NAME);
				value = PrologSimplifier.convert(solution);
				// System.out.println("Prolog solution : " + value);
			}
		} catch (Exception e) {
			throw new IllegalStateException("problem during equation solving using Prolog", e);
		}
		return value;
	}

	public static CodeExpression solvePolynomial(CodeExpression codeExpression, String variableName)
			throws CannotSolveException {
		CodeExpression value = null;
		try {
			InfixExpressionPrinter infixExpressionPrinter = new InfixExpressionPrinter();
			String infixExpression = infixExpressionPrinter.convert(codeExpression);
			// System.out.println("Prolog problem : " + infixExpression);
			Prolog engine = new Prolog();
			InputStream prologCode = PrologSimplifier.class.getResourceAsStream("arith.pl");
			if (prologCode == null) {
				throw new IllegalStateException(PrologSimplifier.class.getResource("arith.pl").toString());
			}
			Theory t = new Theory(prologCode);
			engine.setTheory(t);
			SolveInfo answer = engine.solve("symplify_polynomial(" + infixExpression + "," + variableName + ","
					+ SOLUTION_PROLOG_VARIABLE_NAME + ").");
			if (answer.isSuccess()) {
				Term solution = answer.getTerm(SOLUTION_PROLOG_VARIABLE_NAME);
				value = PrologSimplifier.convert(solution);
				// System.out.println("Prolog solution : " + value);
			}
		} catch (Exception e) {
			throw new IllegalStateException("problem during polynomial solving using Prolog", e);
		}
		if (value == null) {
			throw new CannotSolveException("Invalid solution : " + value);
		}
		return value;
	}

	static CodeExpression convert(Term term) {
		CodeExpression codeExpression = null;
		if (term instanceof Struct) {
			Struct struct = (Struct) term;
			if ("=".equals(struct.getName())) {
				assertArity(struct, 2);
				codeExpression = ComparisonExpression.create(ComparisonOperator.EQUAL, convert(struct.getArg(0)),
						convert(struct.getArg(1)));
			} else if ("+".equals(struct.getName())) {
				assertArity(struct, 2);
				codeExpression = BinaryIntegerExpression.create(BinaryArithmeticOperator.PLUS,
						convert(struct.getArg(0)), convert(struct.getArg(1)));
			} else if ("-".equals(struct.getName())) {
				switch (struct.getArity()) {
				case 1:
					codeExpression = MinusIntegerExpression.create(convert(struct.getArg(0)));
					break;
				case 2:
					codeExpression = BinaryIntegerExpression.create(BinaryArithmeticOperator.MINUS,
							convert(struct.getArg(0)), convert(struct.getArg(1)));
					break;
				default:
					throw new UnsupportedOperationException("Struct : [" + struct.getName() + "] with arity : ["
							+ struct.getArity() + "] not handled.");
				}
			} else if ("*".equals(struct.getName())) {

				assertArity(struct, 2);
				codeExpression = BinaryIntegerExpression.create(BinaryArithmeticOperator.TIMES,
						convert(struct.getArg(0)), convert(struct.getArg(1)));
			} else if ("/".equals(struct.getName())) {
				assertArity(struct, 2);
				codeExpression = BinaryIntegerExpression.create(BinaryArithmeticOperator.DIV, convert(struct.getArg(0)),
						convert(struct.getArg(1)));
			} else if (struct.isAtomic()) {
				// TODO handle types
				codeExpression = new ArithmeticVariableReference(struct.getName(), NumericType.INT);

			} else {
				throw new UnsupportedOperationException("Struct : [" + struct + "], name : [" + struct.getName()
						+ "], class : [" + struct.getClass() + "] not yet handled.");
			}
		} else if (term instanceof Int) {
			Int intVar = (Int) term;
			codeExpression = new IntegerValueExpression(intVar.intValue());
		} else if (term instanceof Var) {
			Var var = (Var) term;
			codeExpression = convert(var.getTerm());
		} else {
			throw new UnsupportedOperationException(
					"Term : [" + term + "] of type : [" + term.getClass() + "] not yet handled.");
		}
		return codeExpression;
	}

	private static void assertArity(Struct struct, int arity) {
		if (struct.getArity() != arity) {
			throw new UnsupportedOperationException(
					"Struct : [" + struct.getName() + "] with arity : [" + struct.getArity() + "] not handled.");
		}
	}

}
