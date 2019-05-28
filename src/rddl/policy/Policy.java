/**
 * RDDL: Implements abstract policy interface.
 * 
 * @author Scott Sanner (ssanner@gmail.com)
 * @version 10/10/10
 *
 **/

package rddl.policy;

import java.util.*;

import org.apache.commons.math3.random.RandomDataGenerator;

import rddl.*;
import rddl.RDDL.*;
import rddl.competition.VisCounter;

public abstract class Policy {
	
	public long RAND_SEED = -1;	

	public RandomDataGenerator _random = new RandomDataGenerator();
	public String _sInstanceName;
	public RDDL _rddl;
	public long _timeAllowed = 0;
	public int currentRound = 0;
	public VisCounter _visCounter;
	public int horizon = 0;
	
	//conformant related
	static public int expectMaxVarDepth = 10;
	static public int maxVarDepth = 10;
	static public double theRatio = -1;
	static public boolean ifConformant = true;
	
	static public int searchDepth = -1;
	static public double avgVarDepth = 0;
	static public double avgUpdates = 0;
	static public double avgSearchDepth = 0;
	static public double effectiveSteps = 0;
	static public double tmpUpdatesChange = 0;
	static public double tmpVarDepthChange = 0;
	static public double tmpSearchDepthChange = 0;
	
	static public int theDepth = 0;
	static public boolean ifReallyRun = false;
	static public boolean ifUseRatio = false;
	static public boolean ifUseFix = false;
	
	static public double numberNodesUpdates = 0;
	static public double timeUsedForCal = 0;
	static public boolean ifFirstStep = false;
	static public double updatesIntotal = 0;
	static public double nodesIntotal = 0;
	static public String algoName = null;
	static public String instanceName = null;
	static public double timeAllowed = 0;
	
	static public LinkedList<Double> timeHis = new LinkedList<>();
	static public LinkedList<Double> nodesupdateHis = new LinkedList<>();
	static public long gradientCost = 0;
	static public long fndalhpaCost = 0;
	//constraints for projection
	// built in buildF, used in projection
	static public ArrayList<ArrayList<Integer>> sumVars = new ArrayList<>();
	static public ArrayList<ArrayList<Integer>> sumCoeffecients = new ArrayList<>();
	static public ArrayList<Integer> sumLimits = new ArrayList<>();
	static public ArrayList<EXPR> sumLimitsExpr = new ArrayList<>();
	static public Boolean[] ifInSumConstraints = null;
	static public ArrayList<Boolean> ifEqual = new ArrayList<>();
	static public boolean ifConstructConstraints = true;
	// const for random policy
	static public ArrayList<Double> randomAction = new ArrayList<>();
	static public int countActBits = 0;
	
	static public Boolean[] ifInGraph = null;
	static public Boolean[] ifForcednotChoose = null;
	//minimal probability of action vars
	//caused by XXXX=>move() preconditions
	//used in projection
	static public ArrayList<Double> minimalProb = new ArrayList<>();
	
	//for constraints
	//used for adding additional effects to 
	static public HashMap<PVAR_NAME, HashMap<ArrayList<TYPE_NAME>, ArrayList<BOOL_EXPR>>> _extraEffects = new HashMap<>();
	static public HashMap<PVAR_NAME, HashMap<ArrayList<TYPE_NAME>, ArrayList<LTERM>>> _extraEffectsLVARS = new HashMap<>();
	//static public HashMap<PVAR_NAME, HashMap<ArrayList<TYPE_NAME>, ArrayList<BOOL_EXPR>>> _forcingConditions = new HashMap<>();

	static public HashMap<PVAR_NAME, HashMap<ArrayList<TYPE_NAME>, ArrayList<BOOL_EXPR>>> _forceActionCondForall = new HashMap<>();
	static public HashMap<PVAR_NAME, HashMap<ArrayList<TYPE_NAME>, ArrayList<LTERM>>> _forcedCondForallLVARS = new HashMap<>();

	static public HashMap<PVAR_NAME, HashMap<ArrayList<TYPE_NAME>, ArrayList<Object>>> _forceActionCondExist = new HashMap<>();
	static public HashMap<PVAR_NAME, HashMap<ArrayList<TYPE_NAME>, ArrayList<LTERM>>> _forcedCondExistLVARS = new HashMap<>();
	
	static public HashMap<TYPE_NAME, LVAR> LVARRecord = new HashMap<>();
	static public HashMap<LVAR, TYPE_NAME> TYPERecord = new HashMap<>();
	static public HashMap<TYPE_NAME, ArrayList<TYPE_NAME>> superClass = new HashMap<>();
	static public HashMap<TYPE_NAME, ArrayList<TYPE_NAME>> childClass = new HashMap<>();
	
	//this mode is used to groups several nodes together into a sum node
	//guarentee the sum is flattened
	//used for a+b=C==k only
	static public boolean groupMode = false;
	
	static public boolean ifPrintSizePredict = false;
	
	static public HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, Integer>> act2Int = new HashMap<>();
	
	//record each step state in the graph
	//used for retreiving satate variable value 
	//when doing projection for XXXXX=>move()
	static public ArrayList<TEState> stateHistory = new ArrayList<>();
	
	//return dynamicDepth / maxVarDepth
	static public double[] DefinePossibleRatio(int numOfTrials) {
		int numTrialInterval = numOfTrials / 3;
		double[] possibleRatios = new double[numTrialInterval];
		double ratioInterval = 1.0 / (numTrialInterval - 1);
		double theRatio = ratioInterval;
		for (int i = 1; i < numTrialInterval; i++) {
			possibleRatios[i] = theRatio;
			theRatio += ratioInterval;
		}
		possibleRatios[0] = 0.0;
		return possibleRatios;
	}

	public Policy() {
		
	}
	
	public Policy(String instance_name) {
		_sInstanceName = instance_name;
	}
	
	public void setInstance(String instance_name) {
		_sInstanceName = instance_name;
	}

	public void setRDDL(RDDL rddl) {
		_rddl = rddl;
	}

	public void setLimitTime(Integer time) {
	}
	
	public int getNumberUpdate() {
		return 0;
	}
	
	public void setVisCounter(VisCounter vis){
		_visCounter = vis;
	}
	
	public void setRandSeed(long rand_seed) {
		RAND_SEED = rand_seed;
		_random = new RandomDataGenerator();
		_random.reSeed(rand_seed);
	}
	
	// Override if needed
	public void roundInit(double time_left, int horizon, int round_number, int total_rounds) {
	}
	
	// Override if needed
	public void roundEnd(double reward) {
		System.out.println("\n*********************************************************");
		System.out.println(">>> ROUND END, reward = " + reward);
		System.out.println("*********************************************************");
	}
	
	// Override if needed
	public void sessionEnd(double total_reward) {
		System.out.println("\n*********************************************************");
		System.out.println(">>> SESSION END, total reward = " + total_reward);
		System.out.println("*********************************************************");
	}
	
	public void setRddlDomain(RDDL rddl){
		_rddl = rddl;
	}
	
	public void setTimeAllowed(long time){
		_timeAllowed = time;
	}
	
	public void setCurrentRound(int round){
		currentRound = round;
	}

	// Must override
	public abstract ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException;
	public ArrayList<PVAR_INST_DEF> EmergencyReturn(State s) throws Exception{
		return new ArrayList<PVAR_INST_DEF>();
	}
	
	public String toString() {
		return "Policy for '" + _sInstanceName + "'";
	}
	
}
