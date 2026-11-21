package net.sf.metacad.revenge.state;

import net.sf.metacad.revenge.type.ClassType;

interface ClassCodeState {

	public abstract void defineClass(ClassType classType);

	public abstract ClassType resolveClass(String className);

}