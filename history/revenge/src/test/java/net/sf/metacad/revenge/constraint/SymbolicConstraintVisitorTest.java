package net.sf.metacad.revenge.constraint;

import static org.junit.Assert.assertEquals;

import java.util.Map;

import org.junit.Test;

import bsh.JavaParser;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.RepeatedExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonOperator;
import net.sf.metacad.revenge.state.CodeState;

public class SymbolicConstraintVisitorTest {

	@Test
	public void testSimpleValue() throws Exception {
		CodeState initialState = JavaParser.evaluate("int a;");
		CodeExpression equation = (CodeExpression) JavaParser.parse("a==42", initialState);
		ConstraintSolver visitor = new SymbolicConstraintVisitor();
		visitor.bindVariable("a_initial", "a_initial", "a");
		visitor.constrain(equation);
		Map<String, CodeExpression> result = visitor.solve("a");
		assertEquals(1, result.size());
		assertEquals(42, ((IntegerValueExpression) result.get("a_initial")).value);
	}

	@Test
	public void testTwoVariables() throws Exception {
		CodeState initialState = JavaParser.evaluate("int a;int b;");
		CodeExpression equation = (CodeExpression) JavaParser.parse("a==-1+b", initialState);
		CodeExpression equation2 = (CodeExpression) JavaParser.parse("b==5", initialState);
		ConstraintSolver visitor = new SymbolicConstraintVisitor();
		visitor.bindVariable("a_initial", "a_initial", "a");
		visitor.bindVariable("b_initial", "b_initial", "b");
		visitor.constrain(equation);
		visitor.constrain(equation2);
		Map<String, CodeExpression> result = visitor.solve("a");
		assertEquals(2, result.size());
		assertEquals(4, ((IntegerValueExpression) result.get("a_initial")).value);
		assertEquals(5, ((IntegerValueExpression) result.get("b_initial")).value);
	}

	@Test
	public void testTwoVariablesRepeat() throws Exception {
		CodeState initialState = JavaParser.evaluate("int a;int b;");
		CodeExpression equation2 = (CodeExpression) JavaParser.parse("b==15", initialState);
		CodeExpression expression = (CodeExpression) JavaParser.parse("(b-1)-1", initialState);
		CodeExpression expression2 = (CodeExpression) JavaParser.parse("a", initialState);
		ConstraintSolver visitor = new SymbolicConstraintVisitor();
		visitor.bindVariable("a_initial", "a_initial", "a");
		visitor.bindVariable("b_initial", "b_initial", "b");
		visitor.constrain(equation2);
		BooleanExpression equation = ComparisonExpression.create(ComparisonOperator.EQUAL, expression2,
				RepeatedExpression.create(expression, new IntegerValueExpression(3), null));
		visitor.constrain(equation);
		Map<String, CodeExpression> result = visitor.solve("a");
		assertEquals(2, result.size());
		assertEquals(9, ((IntegerValueExpression) result.get("a_initial")).value);
		assertEquals(15, ((IntegerValueExpression) result.get("b_initial")).value);
	}

}
