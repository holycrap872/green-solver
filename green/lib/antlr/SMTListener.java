// Generated from SMT.g4 by ANTLR 4.1
package antlr;
import org.antlr.v4.runtime.misc.NotNull;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link SMTParser}.
 */
public interface SMTListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link SMTParser#symbol}.
	 * @param ctx the parse tree
	 */
	void enterSymbol(@NotNull SMTParser.SymbolContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#symbol}.
	 * @param ctx the parse tree
	 */
	void exitSymbol(@NotNull SMTParser.SymbolContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#bool}.
	 * @param ctx the parse tree
	 */
	void enterBool(@NotNull SMTParser.BoolContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#bool}.
	 * @param ctx the parse tree
	 */
	void exitBool(@NotNull SMTParser.BoolContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#nothing}.
	 * @param ctx the parse tree
	 */
	void enterNothing(@NotNull SMTParser.NothingContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#nothing}.
	 * @param ctx the parse tree
	 */
	void exitNothing(@NotNull SMTParser.NothingContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#arraySize}.
	 * @param ctx the parse tree
	 */
	void enterArraySize(@NotNull SMTParser.ArraySizeContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#arraySize}.
	 * @param ctx the parse tree
	 */
	void exitArraySize(@NotNull SMTParser.ArraySizeContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#bitManipulation}.
	 * @param ctx the parse tree
	 */
	void enterBitManipulation(@NotNull SMTParser.BitManipulationContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#bitManipulation}.
	 * @param ctx the parse tree
	 */
	void exitBitManipulation(@NotNull SMTParser.BitManipulationContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#declarations}.
	 * @param ctx the parse tree
	 */
	void enterDeclarations(@NotNull SMTParser.DeclarationsContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#declarations}.
	 * @param ctx the parse tree
	 */
	void exitDeclarations(@NotNull SMTParser.DeclarationsContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#single}.
	 * @param ctx the parse tree
	 */
	void enterSingle(@NotNull SMTParser.SingleContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#single}.
	 * @param ctx the parse tree
	 */
	void exitSingle(@NotNull SMTParser.SingleContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#triple}.
	 * @param ctx the parse tree
	 */
	void enterTriple(@NotNull SMTParser.TripleContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#triple}.
	 * @param ctx the parse tree
	 */
	void exitTriple(@NotNull SMTParser.TripleContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#bvnumber}.
	 * @param ctx the parse tree
	 */
	void enterBvnumber(@NotNull SMTParser.BvnumberContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#bvnumber}.
	 * @param ctx the parse tree
	 */
	void exitBvnumber(@NotNull SMTParser.BvnumberContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#root}.
	 * @param ctx the parse tree
	 */
	void enterRoot(@NotNull SMTParser.RootContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#root}.
	 * @param ctx the parse tree
	 */
	void exitRoot(@NotNull SMTParser.RootContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#doub}.
	 * @param ctx the parse tree
	 */
	void enterDoub(@NotNull SMTParser.DoubContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#doub}.
	 * @param ctx the parse tree
	 */
	void exitDoub(@NotNull SMTParser.DoubContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#arrayDeclaration}.
	 * @param ctx the parse tree
	 */
	void enterArrayDeclaration(@NotNull SMTParser.ArrayDeclarationContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#arrayDeclaration}.
	 * @param ctx the parse tree
	 */
	void exitArrayDeclaration(@NotNull SMTParser.ArrayDeclarationContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#expr}.
	 * @param ctx the parse tree
	 */
	void enterExpr(@NotNull SMTParser.ExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#expr}.
	 * @param ctx the parse tree
	 */
	void exitExpr(@NotNull SMTParser.ExprContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#let}.
	 * @param ctx the parse tree
	 */
	void enterLet(@NotNull SMTParser.LetContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#let}.
	 * @param ctx the parse tree
	 */
	void exitLet(@NotNull SMTParser.LetContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#assertions}.
	 * @param ctx the parse tree
	 */
	void enterAssertions(@NotNull SMTParser.AssertionsContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#assertions}.
	 * @param ctx the parse tree
	 */
	void exitAssertions(@NotNull SMTParser.AssertionsContext ctx);

	/**
	 * Enter a parse tree produced by {@link SMTParser#letexpr}.
	 * @param ctx the parse tree
	 */
	void enterLetexpr(@NotNull SMTParser.LetexprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SMTParser#letexpr}.
	 * @param ctx the parse tree
	 */
	void exitLetexpr(@NotNull SMTParser.LetexprContext ctx);
}