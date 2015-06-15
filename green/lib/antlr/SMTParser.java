// Generated from SMT.g4 by ANTLR 4.1
package antlr;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class SMTParser extends Parser {
	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__10=1, T__9=2, T__8=3, T__7=4, T__6=5, T__5=6, T__4=7, T__3=8, T__2=9, 
		T__1=10, T__0=11, SINGLE=12, DOUB=13, TRIPLE=14, WS=15, ASSERT=16, DECLARE=17, 
		EXTEND=18, EXTRACT=19, BOOLEAN=20, BINARY=21, HEX=22, NUMERAL=23, SYMBOL=24, 
		SIMPLESYMBOL=25, SIMPLESYMBOLSTART=26, SIMPLESYMBOLFINISH=27, QUOTEDSYMBOL=28;
	public static final String[] tokenNames = {
		"<INVALID>", "'()'", "'_ bv'", "'let'", "'(assert'", "'('", "')'", "'(check-sat)'", 
		"'(Array'", "'(set-logic QF_AUFBV )'", "'(_ BitVec'", "'(exit)'", "'empty'", 
		"DOUB", "TRIPLE", "WS", "'assert'", "'declare-fun'", "EXTEND", "'(_ extract'", 
		"BOOLEAN", "BINARY", "HEX", "NUMERAL", "SYMBOL", "SIMPLESYMBOL", "SIMPLESYMBOLSTART", 
		"SIMPLESYMBOLFINISH", "'|a|'"
	};
	public static final int
		RULE_root = 0, RULE_declarations = 1, RULE_arrayDeclaration = 2, RULE_arraySize = 3, 
		RULE_assertions = 4, RULE_expr = 5, RULE_triple = 6, RULE_doub = 7, RULE_single = 8, 
		RULE_nothing = 9, RULE_let = 10, RULE_letexpr = 11, RULE_bitManipulation = 12, 
		RULE_bvnumber = 13, RULE_bool = 14, RULE_symbol = 15;
	public static final String[] ruleNames = {
		"root", "declarations", "arrayDeclaration", "arraySize", "assertions", 
		"expr", "triple", "doub", "single", "nothing", "let", "letexpr", "bitManipulation", 
		"bvnumber", "bool", "symbol"
	};

	@Override
	public String getGrammarFileName() { return "SMT.g4"; }

	@Override
	public String[] getTokenNames() { return tokenNames; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public SMTParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}
	public static class RootContext extends ParserRuleContext {
		public AssertionsContext assertions() {
			return getRuleContext(AssertionsContext.class,0);
		}
		public DeclarationsContext declarations() {
			return getRuleContext(DeclarationsContext.class,0);
		}
		public RootContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_root; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterRoot(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitRoot(this);
		}
	}

	public final RootContext root() throws RecognitionException {
		RootContext _localctx = new RootContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_root);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(32); match(9);
			setState(33); declarations();
			setState(34); assertions();
			setState(35); match(7);
			setState(36); match(11);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class DeclarationsContext extends ParserRuleContext {
		public TerminalNode DECLARE(int i) {
			return getToken(SMTParser.DECLARE, i);
		}
		public List<ArrayDeclarationContext> arrayDeclaration() {
			return getRuleContexts(ArrayDeclarationContext.class);
		}
		public List<TerminalNode> DECLARE() { return getTokens(SMTParser.DECLARE); }
		public SymbolContext symbol(int i) {
			return getRuleContext(SymbolContext.class,i);
		}
		public List<SymbolContext> symbol() {
			return getRuleContexts(SymbolContext.class);
		}
		public ArrayDeclarationContext arrayDeclaration(int i) {
			return getRuleContext(ArrayDeclarationContext.class,i);
		}
		public DeclarationsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_declarations; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterDeclarations(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitDeclarations(this);
		}
	}

	public final DeclarationsContext declarations() throws RecognitionException {
		DeclarationsContext _localctx = new DeclarationsContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_declarations);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(47);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==5) {
				{
				{
				setState(38); match(5);
				setState(39); match(DECLARE);
				setState(40); symbol();
				setState(41); match(1);
				setState(42); arrayDeclaration();
				setState(43); match(6);
				}
				}
				setState(49);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ArrayDeclarationContext extends ParserRuleContext {
		public List<ArraySizeContext> arraySize() {
			return getRuleContexts(ArraySizeContext.class);
		}
		public ArraySizeContext arraySize(int i) {
			return getRuleContext(ArraySizeContext.class,i);
		}
		public ArrayDeclarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_arrayDeclaration; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterArrayDeclaration(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitArrayDeclaration(this);
		}
	}

	public final ArrayDeclarationContext arrayDeclaration() throws RecognitionException {
		ArrayDeclarationContext _localctx = new ArrayDeclarationContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_arrayDeclaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(50); match(8);
			setState(51); arraySize();
			setState(52); arraySize();
			setState(53); match(6);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ArraySizeContext extends ParserRuleContext {
		public TerminalNode NUMERAL() { return getToken(SMTParser.NUMERAL, 0); }
		public ArraySizeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_arraySize; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterArraySize(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitArraySize(this);
		}
	}

	public final ArraySizeContext arraySize() throws RecognitionException {
		ArraySizeContext _localctx = new ArraySizeContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_arraySize);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(55); match(10);
			setState(56); match(NUMERAL);
			setState(57); match(6);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssertionsContext extends ParserRuleContext {
		public List<ExprContext> expr() {
			return getRuleContexts(ExprContext.class);
		}
		public ExprContext expr(int i) {
			return getRuleContext(ExprContext.class,i);
		}
		public AssertionsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertions; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterAssertions(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitAssertions(this);
		}
	}

	public final AssertionsContext assertions() throws RecognitionException {
		AssertionsContext _localctx = new AssertionsContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_assertions);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(63); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(59); match(4);
				setState(60); expr();
				setState(61); match(6);
				}
				}
				setState(65); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==4 );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExprContext extends ParserRuleContext {
		public SymbolContext symbol() {
			return getRuleContext(SymbolContext.class,0);
		}
		public BvnumberContext bvnumber() {
			return getRuleContext(BvnumberContext.class,0);
		}
		public NothingContext nothing() {
			return getRuleContext(NothingContext.class,0);
		}
		public SingleContext single() {
			return getRuleContext(SingleContext.class,0);
		}
		public DoubContext doub() {
			return getRuleContext(DoubContext.class,0);
		}
		public BoolContext bool() {
			return getRuleContext(BoolContext.class,0);
		}
		public TripleContext triple() {
			return getRuleContext(TripleContext.class,0);
		}
		public ExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitExpr(this);
		}
	}

	public final ExprContext expr() throws RecognitionException {
		ExprContext _localctx = new ExprContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_expr);
		try {
			setState(79);
			switch (_input.LA(1)) {
			case 5:
				enterOuterAlt(_localctx, 1);
				{
				setState(67); match(5);
				setState(73);
				switch (_input.LA(1)) {
				case 5:
				case EXTEND:
				case EXTRACT:
				case BOOLEAN:
				case SYMBOL:
					{
					setState(68); nothing();
					}
					break;
				case 3:
				case SINGLE:
					{
					setState(69); single();
					}
					break;
				case DOUB:
					{
					setState(70); doub();
					}
					break;
				case TRIPLE:
					{
					setState(71); triple();
					}
					break;
				case 2:
					{
					setState(72); bvnumber();
					}
					break;
				default:
					throw new NoViableAltException(this);
				}
				setState(75); match(6);
				}
				break;
			case SYMBOL:
				enterOuterAlt(_localctx, 2);
				{
				setState(77); symbol();
				}
				break;
			case BOOLEAN:
				enterOuterAlt(_localctx, 3);
				{
				setState(78); bool();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TripleContext extends ParserRuleContext {
		public List<ExprContext> expr() {
			return getRuleContexts(ExprContext.class);
		}
		public ExprContext expr(int i) {
			return getRuleContext(ExprContext.class,i);
		}
		public TerminalNode TRIPLE() { return getToken(SMTParser.TRIPLE, 0); }
		public TripleContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_triple; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterTriple(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitTriple(this);
		}
	}

	public final TripleContext triple() throws RecognitionException {
		TripleContext _localctx = new TripleContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_triple);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(81); match(TRIPLE);
			setState(82); expr();
			setState(83); expr();
			setState(84); expr();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class DoubContext extends ParserRuleContext {
		public TerminalNode DOUB() { return getToken(SMTParser.DOUB, 0); }
		public List<ExprContext> expr() {
			return getRuleContexts(ExprContext.class);
		}
		public ExprContext expr(int i) {
			return getRuleContext(ExprContext.class,i);
		}
		public DoubContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_doub; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterDoub(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitDoub(this);
		}
	}

	public final DoubContext doub() throws RecognitionException {
		DoubContext _localctx = new DoubContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_doub);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(86); match(DOUB);
			setState(87); expr();
			setState(88); expr();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SingleContext extends ParserRuleContext {
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public LetContext let() {
			return getRuleContext(LetContext.class,0);
		}
		public TerminalNode SINGLE() { return getToken(SMTParser.SINGLE, 0); }
		public SingleContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_single; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterSingle(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitSingle(this);
		}
	}

	public final SingleContext single() throws RecognitionException {
		SingleContext _localctx = new SingleContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_single);
		try {
			setState(93);
			switch (_input.LA(1)) {
			case SINGLE:
				enterOuterAlt(_localctx, 1);
				{
				setState(90); match(SINGLE);
				setState(91); expr();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 2);
				{
				setState(92); let();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class NothingContext extends ParserRuleContext {
		public BitManipulationContext bitManipulation() {
			return getRuleContext(BitManipulationContext.class,0);
		}
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public NothingContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_nothing; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterNothing(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitNothing(this);
		}
	}

	public final NothingContext nothing() throws RecognitionException {
		NothingContext _localctx = new NothingContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_nothing);
		try {
			setState(99);
			switch (_input.LA(1)) {
			case 5:
			case BOOLEAN:
			case SYMBOL:
				enterOuterAlt(_localctx, 1);
				{
				setState(95); expr();
				}
				break;
			case EXTEND:
			case EXTRACT:
				enterOuterAlt(_localctx, 2);
				{
				setState(96); bitManipulation();
				setState(97); expr();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class LetContext extends ParserRuleContext {
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public LetexprContext letexpr(int i) {
			return getRuleContext(LetexprContext.class,i);
		}
		public List<LetexprContext> letexpr() {
			return getRuleContexts(LetexprContext.class);
		}
		public LetContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_let; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterLet(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitLet(this);
		}
	}

	public final LetContext let() throws RecognitionException {
		LetContext _localctx = new LetContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_let);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(101); match(3);
			setState(102); match(5);
			setState(104); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(103); letexpr();
				}
				}
				setState(106); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==5 );
			setState(108); match(6);
			setState(109); expr();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class LetexprContext extends ParserRuleContext {
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public TerminalNode SYMBOL() { return getToken(SMTParser.SYMBOL, 0); }
		public LetexprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_letexpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterLetexpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitLetexpr(this);
		}
	}

	public final LetexprContext letexpr() throws RecognitionException {
		LetexprContext _localctx = new LetexprContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_letexpr);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(111); match(5);
			setState(112); match(SYMBOL);
			setState(113); expr();
			setState(114); match(6);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BitManipulationContext extends ParserRuleContext {
		public List<TerminalNode> NUMERAL() { return getTokens(SMTParser.NUMERAL); }
		public TerminalNode EXTRACT() { return getToken(SMTParser.EXTRACT, 0); }
		public TerminalNode NUMERAL(int i) {
			return getToken(SMTParser.NUMERAL, i);
		}
		public TerminalNode EXTEND() { return getToken(SMTParser.EXTEND, 0); }
		public BitManipulationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_bitManipulation; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterBitManipulation(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitBitManipulation(this);
		}
	}

	public final BitManipulationContext bitManipulation() throws RecognitionException {
		BitManipulationContext _localctx = new BitManipulationContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_bitManipulation);
		try {
			setState(123);
			switch (_input.LA(1)) {
			case EXTEND:
				enterOuterAlt(_localctx, 1);
				{
				setState(116); match(EXTEND);
				setState(117); match(NUMERAL);
				setState(118); match(6);
				}
				break;
			case EXTRACT:
				enterOuterAlt(_localctx, 2);
				{
				setState(119); match(EXTRACT);
				setState(120); match(NUMERAL);
				setState(121); match(NUMERAL);
				setState(122); match(6);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BvnumberContext extends ParserRuleContext {
		public List<TerminalNode> NUMERAL() { return getTokens(SMTParser.NUMERAL); }
		public TerminalNode NUMERAL(int i) {
			return getToken(SMTParser.NUMERAL, i);
		}
		public BvnumberContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_bvnumber; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterBvnumber(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitBvnumber(this);
		}
	}

	public final BvnumberContext bvnumber() throws RecognitionException {
		BvnumberContext _localctx = new BvnumberContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_bvnumber);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(125); match(2);
			setState(126); match(NUMERAL);
			setState(127); match(NUMERAL);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BoolContext extends ParserRuleContext {
		public TerminalNode BOOLEAN() { return getToken(SMTParser.BOOLEAN, 0); }
		public BoolContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_bool; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterBool(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitBool(this);
		}
	}

	public final BoolContext bool() throws RecognitionException {
		BoolContext _localctx = new BoolContext(_ctx, getState());
		enterRule(_localctx, 28, RULE_bool);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(129); match(BOOLEAN);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SymbolContext extends ParserRuleContext {
		public TerminalNode SYMBOL() { return getToken(SMTParser.SYMBOL, 0); }
		public SymbolContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_symbol; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).enterSymbol(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SMTListener ) ((SMTListener)listener).exitSymbol(this);
		}
	}

	public final SymbolContext symbol() throws RecognitionException {
		SymbolContext _localctx = new SymbolContext(_ctx, getState());
		enterRule(_localctx, 30, RULE_symbol);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(131); match(SYMBOL);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\3\uacf5\uee8c\u4f5d\u8b0d\u4a45\u78bd\u1b2f\u3378\3\36\u0088\4\2\t\2"+
		"\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\3\2\3\2"+
		"\3\2\3\2\3\2\3\2\3\3\3\3\3\3\3\3\3\3\3\3\3\3\7\3\60\n\3\f\3\16\3\63\13"+
		"\3\3\4\3\4\3\4\3\4\3\4\3\5\3\5\3\5\3\5\3\6\3\6\3\6\3\6\6\6B\n\6\r\6\16"+
		"\6C\3\7\3\7\3\7\3\7\3\7\3\7\5\7L\n\7\3\7\3\7\3\7\3\7\5\7R\n\7\3\b\3\b"+
		"\3\b\3\b\3\b\3\t\3\t\3\t\3\t\3\n\3\n\3\n\5\n`\n\n\3\13\3\13\3\13\3\13"+
		"\5\13f\n\13\3\f\3\f\3\f\6\fk\n\f\r\f\16\fl\3\f\3\f\3\f\3\r\3\r\3\r\3\r"+
		"\3\r\3\16\3\16\3\16\3\16\3\16\3\16\3\16\5\16~\n\16\3\17\3\17\3\17\3\17"+
		"\3\20\3\20\3\21\3\21\3\21\2\22\2\4\6\b\n\f\16\20\22\24\26\30\32\34\36"+
		" \2\2\u0083\2\"\3\2\2\2\4\61\3\2\2\2\6\64\3\2\2\2\b9\3\2\2\2\nA\3\2\2"+
		"\2\fQ\3\2\2\2\16S\3\2\2\2\20X\3\2\2\2\22_\3\2\2\2\24e\3\2\2\2\26g\3\2"+
		"\2\2\30q\3\2\2\2\32}\3\2\2\2\34\177\3\2\2\2\36\u0083\3\2\2\2 \u0085\3"+
		"\2\2\2\"#\7\13\2\2#$\5\4\3\2$%\5\n\6\2%&\7\t\2\2&\'\7\r\2\2\'\3\3\2\2"+
		"\2()\7\7\2\2)*\7\23\2\2*+\5 \21\2+,\7\3\2\2,-\5\6\4\2-.\7\b\2\2.\60\3"+
		"\2\2\2/(\3\2\2\2\60\63\3\2\2\2\61/\3\2\2\2\61\62\3\2\2\2\62\5\3\2\2\2"+
		"\63\61\3\2\2\2\64\65\7\n\2\2\65\66\5\b\5\2\66\67\5\b\5\2\678\7\b\2\28"+
		"\7\3\2\2\29:\7\f\2\2:;\7\31\2\2;<\7\b\2\2<\t\3\2\2\2=>\7\6\2\2>?\5\f\7"+
		"\2?@\7\b\2\2@B\3\2\2\2A=\3\2\2\2BC\3\2\2\2CA\3\2\2\2CD\3\2\2\2D\13\3\2"+
		"\2\2EK\7\7\2\2FL\5\24\13\2GL\5\22\n\2HL\5\20\t\2IL\5\16\b\2JL\5\34\17"+
		"\2KF\3\2\2\2KG\3\2\2\2KH\3\2\2\2KI\3\2\2\2KJ\3\2\2\2LM\3\2\2\2MN\7\b\2"+
		"\2NR\3\2\2\2OR\5 \21\2PR\5\36\20\2QE\3\2\2\2QO\3\2\2\2QP\3\2\2\2R\r\3"+
		"\2\2\2ST\7\20\2\2TU\5\f\7\2UV\5\f\7\2VW\5\f\7\2W\17\3\2\2\2XY\7\17\2\2"+
		"YZ\5\f\7\2Z[\5\f\7\2[\21\3\2\2\2\\]\7\16\2\2]`\5\f\7\2^`\5\26\f\2_\\\3"+
		"\2\2\2_^\3\2\2\2`\23\3\2\2\2af\5\f\7\2bc\5\32\16\2cd\5\f\7\2df\3\2\2\2"+
		"ea\3\2\2\2eb\3\2\2\2f\25\3\2\2\2gh\7\5\2\2hj\7\7\2\2ik\5\30\r\2ji\3\2"+
		"\2\2kl\3\2\2\2lj\3\2\2\2lm\3\2\2\2mn\3\2\2\2no\7\b\2\2op\5\f\7\2p\27\3"+
		"\2\2\2qr\7\7\2\2rs\7\32\2\2st\5\f\7\2tu\7\b\2\2u\31\3\2\2\2vw\7\24\2\2"+
		"wx\7\31\2\2x~\7\b\2\2yz\7\25\2\2z{\7\31\2\2{|\7\31\2\2|~\7\b\2\2}v\3\2"+
		"\2\2}y\3\2\2\2~\33\3\2\2\2\177\u0080\7\4\2\2\u0080\u0081\7\31\2\2\u0081"+
		"\u0082\7\31\2\2\u0082\35\3\2\2\2\u0083\u0084\7\26\2\2\u0084\37\3\2\2\2"+
		"\u0085\u0086\7\32\2\2\u0086!\3\2\2\2\n\61CKQ_el}";
	public static final ATN _ATN =
		ATNSimulator.deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}