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

/**
 * TODO add a test assuring that mute variables disappear from expressions since they will be dropped. Example : int x =
 * 0; {int y = x; y++; x = y;} final value for x must be increment(x) not increment(y) because y will disapper when
 * out-of scope. This is also a precondition for handling placeholders in while loops, that currently ignore scoped
 * cycles.
 * 
 * @author Luca Dall'Olio
 * 
 */
public class BlockStatementTest {

	@Test
	public void testEvaluate() throws Exception {
		String def1 = "int var1 = 1; int var3 = 3; {int var2; var2 = 2; var3 = 42; int var1 = 7; }";
		StateTransition statement = JavaParser.parse(def1);
		CodeState finalState = statement.evaluate(new ProgramState());
		assertNotNull(finalState);
		assertEquals(MetaExpression.NO_LEFT_VALUE, finalState.getLeftValue());
		assertEquals(MetaExpression.NOT_DEFINED_VARIABLE, finalState.variableValue("var2"));
		assertEquals(1, ((IntegerValueExpression) finalState.variableValue("var1")).value);
		assertEquals(42, ((IntegerValueExpression) finalState.variableValue("var3")).value);
	}

}
