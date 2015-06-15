package za.ac.sun.cs.green.klee;

import static org.junit.Assert.*;

import java.io.File;
import java.io.FileInputStream;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;
import java.util.Set;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import za.ac.sun.cs.green.Constants;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.parser.klee.KleeOutputParser;
import za.ac.sun.cs.green.resources.Pair;
import za.ac.sun.cs.green.service.bvfactorizer.BVFactorExpression;
import za.ac.sun.cs.green.util.Configuration;

public class FactorSmasherTest {

	private static Green solver;
	private static Properties props;
	
	@BeforeClass
	public static void buildUp(){
		props = new Properties();
		try {
			props.load(new FileInputStream("test/za/ac/sun/cs/green/klee/files/klee.properties"));
		} catch (Exception e) {
			System.err.println("Problem loading .properties file");
			System.exit(1);
		}
		solver = new Green(props);
		new Configuration(solver, props).configure();
	}


	@Test
	public void test00() {

		StringBuilder unparsed = new StringBuilder();;
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun n_args () (Array (_ BitVec 32) (_ BitVec 8) ) )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 8) ) )");
		unparsed.append("(declare-fun arg0 () (Array (_ BitVec 32) (_ BitVec 8) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv32 8) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv1 32) ) (_ bv39 8) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv178 8) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv3 32) ) (_ bv5 8) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv4 32) ) (_ bv0 8) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv5 32) ) (_ bv0 8) ) )");
		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());

		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		assertEquals(bvf.getFactors().size(), 6);
	}

	@Test
	public void test01() {

		StringBuilder unparsed = new StringBuilder();
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv32 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv1 32) ) (_ bv39 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv3 32) ) (_ bv5 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv4 32) ) (_ bv0 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv0 32) ) ) (_ bv32 32) ) )");
		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());

		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		assertEquals(bvf.getFactors().size(), 5);
	}


	@Test
	public void test02() {

		StringBuilder unparsed = new StringBuilder();
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv2 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv1 32) ) (_ bv39 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv3 32) ) (_ bv5 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv4 32) ) (_ bv0 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv0 32) ) ) (_ bv178 32) ) )");
		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());

		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		assertEquals(bvf.getFactors().size(), 4);
	}
	
	@Test
	public void test021() {

		StringBuilder unparsed = new StringBuilder();
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv0 32) ) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv0 32) ) ) (_ bv179 32) ) )");
		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());

		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		assertEquals(bvf.getFactors().size(), 1);
	}

	@Test
	public void test03() {

		StringBuilder unparsed = new StringBuilder();
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv2 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv1 32) ) (_ bv3 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv0 32) ) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv1 32) ) ) (_ bv5 32) ) )");
		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());

		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		Set<Expression> set = bvf.getFactors();
		for(Expression e :set){
			System.out.println(e.toString() +"\n\n");
		}
		assertEquals(set.size(), 1);
	}

	
	@Test
	public void test04() {

		StringBuilder unparsed = new StringBuilder();
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv2 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv1 32) ) (_ bv3 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv3 32) ) (_ bv5 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv4 32) ) (_ bv0 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv0 32) ) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv1 32) ) ) (_ bv5 32) ) )");
		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());


		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		Set<Expression> set = bvf.getFactors();
		for(Expression e :set){
			System.out.println(e.toString() +"\n\n");
		}
		assertEquals(set.size(), 2);
	}
	
	@Test
	public void test041() {

		StringBuilder unparsed = new StringBuilder();
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv2 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv1 32) ) (_ bv3 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv4 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv3 32) ) (_ bv170 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv4 32) ) (_ bv0 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (select const_arr1 (_ bv0 32) ) ) ) (_ bv0 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv1 32) ) ) (_ bv170 32) ) )");
		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());

		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		Set<Expression> set = bvf.getFactors();
		for(Expression e :set){
			System.out.println(e.toString() +"\n\n");
		}
		assertEquals(set.size(), 1);
	}
	
	@Test
	public void test042() {

		StringBuilder unparsed = new StringBuilder();
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv2 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv1 32) ) (_ bv3 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv4 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv3 32) ) (_ bv170 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv4 32) ) (_ bv1 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (select const_arr1 (_ bv0 32) ) ) ) (_ bv0 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv1 32) ) ) (_ bv170 32) ) )");
		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());

		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		Set<Expression> set = bvf.getFactors();
		for(Expression e :set){
			System.out.println(e.toString() +"\n\n");
		}
				
		assertEquals(set.size(), 1);
	}
	
	@Test
	public void test05() {

		StringBuilder unparsed = new StringBuilder();
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv2 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv1 32) ) (_ bv3 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv3 32) ) (_ bv5 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv4 32) ) (_ bv0 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv0 32) ) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv1 32) ) ) (_ bv5 32) ) )");
		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());

		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		Set<Expression> set = bvf.getFactors();
		for(Expression e :set){
			System.out.println(e.toString() +"\n\n");
		}
		assertEquals(set.size(), 2);
	}

	@Test
	public void test06() {

		StringBuilder unparsed = new StringBuilder();
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv2 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv1 32) ) (_ bv3 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv3 32) ) (_ bv5 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv4 32) ) (_ bv0 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv0 32) ) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv1 32) ) ) (_ bv5 32) ) )");
		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());

		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		assertEquals(bvf.getFactors().size(), 2);
	}

	@Test
	public void test07() {

		StringBuilder unparsed = new StringBuilder();
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv2 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv1 32) ) (_ bv3 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv3 32) ) (_ bv5 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv4 32) ) (_ bv0 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv0 32) ) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv1 32) ) ) (_ bv5 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv5 32) ) ) (_ bv5 32) ) )");

		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());

		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		assertEquals(bvf.getFactors().size(), 1);
	}
	
	@Test
	public void test071() {

		StringBuilder unparsed = new StringBuilder();
		unparsed.append("(set-logic QF_AUFBV )");
		unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv2 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv1 32) ) (_ bv3 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv3 32) ) (_ bv5 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (_ bv4 32) ) (_ bv0 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv0 32) ) ) (_ bv178 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv1 32) ) ) (_ bv5 32) ) )");
		unparsed.append("(assert (=  (select const_arr1 (select const_arr1 (_ bv5 32) ) ) (_ bv5 32) ) )");
		
		unparsed.append("(check-sat)");
		unparsed.append("(exit)");

		Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());

		BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

		assertEquals(bvf.getFactors().size(), 1);
	}

	@Test
	public void test08() {

		for(int i = 0; i < 1; i ++){
			StringBuilder unparsed = new StringBuilder();
			unparsed.append("(set-logic QF_AUFBV )");
			unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");

			List<String> mix = new LinkedList<String>();
			mix.add("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv2 32) ) )");
			mix.add("(assert (=  (select const_arr1 (_ bv1 32) ) (_ bv3 32) ) )");
			mix.add("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv178 32) ) )");
			mix.add("(assert (=  (select const_arr1 (_ bv3 32) ) (_ bv5 32) ) )");
			mix.add("(assert (=  (select const_arr1 (_ bv4 32) ) (_ bv0 32) ) )");
			mix.add("(assert (=  (select const_arr1 (select const_arr1 (_ bv0 32) ) ) (_ bv178 32) ) )");
			mix.add("(assert (=  (select const_arr1 (select const_arr1 (_ bv1 32) ) ) (_ bv5 32) ) )");
			mix.add("(assert (=  (select const_arr1 (select const_arr1 (_ bv5 32) ) ) (_ bv5 32) ) )");

			Collections.shuffle(mix);

			for(String s : mix){
				unparsed.append(s);
			}
			unparsed.append("(check-sat)");
			unparsed.append("(exit)");

			Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());

			BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);

			assertEquals(bvf.getFactors().size(), 1);
		}
	}
	
	@Test
	public void test09() {

		for(int i = 0; i < 100; i ++){
			StringBuilder unparsed = new StringBuilder();
			unparsed.append("(set-logic QF_AUFBV )");
			unparsed.append("(declare-fun const_arr1 () (Array (_ BitVec 32) (_ BitVec 32) ) )");

			List<String> mix = new LinkedList<String>();
			mix.add("(assert (=  (select const_arr1 (_ bv0 32) ) (_ bv2 32) ) )");
			mix.add("(assert (=  (select const_arr1 (_ bv1 32) ) (_ bv3 32) ) )");
			mix.add("(assert (=  (select const_arr1 (_ bv2 32) ) (_ bv178 32) ) )");
			mix.add("(assert (=  (select const_arr1 (_ bv3 32) ) (_ bv5 32) ) )");
			mix.add("(assert (=  (select const_arr1 (_ bv4 32) ) (_ bv0 32) ) )");
			mix.add("(assert (=  (select const_arr1 (_ bv5 32) ) (_ bv8 32) ) )");
			mix.add("(assert (=  (select const_arr1 (select const_arr1 (_ bv0 32) ) ) (_ bv178 32) ) )");
			mix.add("(assert (=  (select const_arr1 (select const_arr1 (_ bv1 32) ) ) (_ bv5 32) ) )");
			mix.add("(assert (bvsge  (select const_arr1 (_ bv6 32) ) (_ bv0 32) ) )");
			mix.add("(assert (bvsle  (select const_arr1 (_ bv6 32) ) (_ bv1 32) ) )");
			mix.add("(assert (=  (select const_arr1 (select const_arr1 (_ bv6 32) ) ) (_ bv3 32) ) )");
			
			Collections.shuffle(mix);

			for(String s : mix){
				unparsed.append(s);
			}
			unparsed.append("(check-sat)");
			unparsed.append("(exit)");

			Expression expression = KleeOutputParser.createExpressionKlee(unparsed.toString());

			BVFactorExpression bvf = new BVFactorExpression(solver, null, expression, props);
			
			Set<Expression> set = bvf.getFactors();
			for(Expression e :set){
				System.out.println(e.toString() +"\n\n");
			}
			assertEquals(set.size(), 3);
		}
	}

	
	@Test
	public void test010(){
		KleeOutputParser kp = new KleeOutputParser(new File("test/za/ac/sun/cs/green/klee/files/query110"));
		
		assertTrue(kp.hasNext());
		Pair<Expression, Boolean> pair = kp.getNext();
		BVFactorExpression bvf = new BVFactorExpression(solver, null, pair.first, props);

		assertEquals(bvf.getFactors().size(), 17);
	}

	@Test
	public void test11(){
		KleeOutputParser kp = new KleeOutputParser(new File("test/za/ac/sun/cs/green/klee/files/query110"));
		
		assertTrue(kp.hasNext());
		Pair<Expression, Boolean> pair = kp.getNext();

		String holder = props.getProperty(Constants.SMASH_FACTORS_KEY);
		props.setProperty(Constants.SMASH_FACTORS_KEY, "no");
		BVFactorExpression bvf = new BVFactorExpression(solver, null, pair.first, props);
		props.setProperty(Constants.SMASH_FACTORS_KEY, holder);

		assertEquals(bvf.getFactors().size(), 1);
	}
	
	@AfterClass
	public static void tearDown(){
		solver.report();
	}
}
