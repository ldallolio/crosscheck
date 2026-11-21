package net.sf.metacad.revenge.state;

public interface WrappingState extends CodeState {
	void setWrappedState(CodeState wrappedState);

	void purge();
}
