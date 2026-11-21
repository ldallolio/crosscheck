package net.sf.metacad.revenge.constraint;

import static org.junit.Assert.assertNotNull;

import org.junit.Test;

import bsh.JavaParser;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.IntegerSymbolicExpression;
import net.sf.metacad.revenge.expression.arithmetic.BinaryArithmeticOperator;
import net.sf.metacad.revenge.expression.arithmetic.BinaryIntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerPlaceholder;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonOperator;
import net.sf.metacad.revenge.state.CodeState;

public class PrologSimplifierTest {

	@Test
	public void test() throws Exception {
		CodeState initialState = JavaParser.evaluate("int a;");
		CodeExpression equation = (CodeExpression) JavaParser.parse("a==0", initialState);
		CodeExpression solution = PrologSimplifier.solveEquation(equation, "a");
		assertNotNull(solution);
	}

	@Test
	public void testRational() throws Exception {
		CodeState initialState = JavaParser.evaluate("int a;");
		CodeExpression equation = (CodeExpression) JavaParser.parse("a==3*(2/3)", initialState);
		CodeExpression solution = PrologSimplifier.solveEquation(equation, "a");
		assertNotNull(solution);
	}

	@Test
	public void testSymbolAndUnknown() throws Exception {
		IntegerSymbolicExpression randomSymbol = new IntegerSymbolicExpression("random", "random", null);
		IntegerPlaceholder steps = new IntegerPlaceholder("steps");
		CodeExpression leftSide = BinaryIntegerExpression.create(BinaryArithmeticOperator.PLUS, randomSymbol,
				steps);
		BooleanExpression equation = ComparisonExpression.create(ComparisonOperator.EQUAL, leftSide,
				new IntegerValueExpression(13));
		CodeExpression solution = PrologSimplifier.solveEquation(equation, "steps");
		assertNotNull(solution);
	}

}
