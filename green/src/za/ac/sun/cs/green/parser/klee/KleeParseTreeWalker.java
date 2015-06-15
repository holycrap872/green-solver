package za.ac.sun.cs.green.parser.klee;

import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeListener;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;

public class KleeParseTreeWalker extends ParseTreeWalker{
	public KleeParseTreeWalker(){
		super();
	}
	
	public void walk(ParseTreeListener listener, ParseTree t) {
		if ( t instanceof ErrorNode) {
			listener.visitErrorNode((ErrorNode)t);
			return;
		}
		else if ( t instanceof TerminalNode) {
			listener.visitTerminal((TerminalNode)t);
			return;
		}
		RuleNode r = (RuleNode)t;
		enterRule(listener, r);
		int n = r.getChildCount();
		for (int i = 0; i<n; i++) {
			walk(listener, r.getChild(i));
		}
		exitRule(listener, r);

	}
}
