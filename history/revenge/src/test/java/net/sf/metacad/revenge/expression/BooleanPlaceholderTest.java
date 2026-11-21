package net.sf.metacad.revenge.expression;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanOperator;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.BooleanPlaceholder;
import net.sf.metacad.revenge.state.CodeState;

import org.junit.Test;

import bsh.JavaParser;

public class BooleanPlaceholderTest {

	@Test
	public void testNotSimplified() {
		BooleanPlaceholder a1 = new BooleanPlaceholder("a1");
		BooleanPlaceholder b1 = new BooleanPlaceholder("b1");
		BooleanExpression orExpr = BinaryBooleanExpression.create(BinaryBooleanOperator.OR, a1, b1);
		assertTrue(orExpr instanceof BinaryBooleanExpression);
	}

	@Test
	public void testAssignment() throws Exception {
		CodeState initialState = JavaParser.evaluate("boolean b;");
		BooleanPlaceholder b1 = new BooleanPlaceholder("b1");
		initialState.assignVariable("b", b1);
		assertEquals(b1, initialState.variableValue("b"));
	}

}
