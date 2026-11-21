package net.sf.metacad.revenge.statement;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import net.sf.metacad.revenge.expression.MetaExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.ProgramState;
import net.sf.metacad.revenge.state.StateTransition;

import org.junit.Test;

import bsh.JavaParser;

public class IfStatementTest {

	@Test
	public void testEvaluate() throws Exception {

		StateTransition ifStatement = JavaParser.parse("int var1 = 1; if (true) var1 = 42;");

		CodeState finalState = ifStatement.evaluate(new ProgramState());
		assertNotNull(finalState);
		assertEquals(MetaExpression.NO_LEFT_VALUE, finalState.getLeftValue());
		assertEquals(new IntegerValueExpression(42), finalState.variableValue("var1"));
	}

	@Test
	public void testEvaluateWithFollowup() throws Exception {

		StateTransition ifStatement = JavaParser.parse("int var1 = 1; if (true) var1 = 42; var1 = var1+1;");

		CodeState finalState = ifStatement.evaluate(new ProgramState());
		assertNotNull(finalState);
		assertEquals(new IntegerValueExpression(43), finalState.variableValue("var1"));
	}

}
