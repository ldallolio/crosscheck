package net.sf.metacad.revenge.definition;

import java.io.Serializable;

import net.sf.metacad.revenge.state.StateTransition;

/**
 * <p>
 * Many languages (e.g. C) make a distinction between statements and definitions, with a statement only containing
 * executable code and a definition declaring an identifier.
 * </p>
 * 
 * @author ldallolio
 * 
 */
public interface CodeDefinition extends StateTransition, Serializable {

}
