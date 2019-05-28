package rddl.policy;


import rddl.competition.Records;

import java.lang.reflect.Array;
import java.util.*;


import org.apache.commons.math3.random.RandomDataGenerator;

import rddl.TreeExp;
import rddl.TEState;
import rddl.EvalException;
import rddl.RDDL;
import rddl.RDDL.*;
import rddl.State;

import rddl.*;

public class N_F extends Policy {
	
	public N_F () {
		super();
	}
	
	public N_F(String instance_name) {
		super(instance_name);
		Global.ifLift = false;
		Global.ifRecordLift = false;
		searchDepth = -1;
		expectMaxVarDepth = 50;
		ifConformant = false;
	}
	
	boolean ifConverge = false;
	final double convergeNorm = 0.01;
	//if we only do certain nubber of pdates
	//we cannot see the overall trends of ratio action seen/updates
	//so we use this to adjust our estimate
	//so action seen at each step = actionSeen / staCounter * actionEstimateAdj
	final double actionEstimateAdj = 1;
	
	//double alpha = 0.00001;
	//convergence threashold
	//this is just init value. it will be adjusted by another par
	double ConvergeT = 0.0000001;
	
	//the portion of time spent on sampling final actions, given the marginal prob of each bit
	final double SampleTime = 0.2;
	//how many times do we wanna update each action bit
	int numOfIte = 200;
	
	//if trySeeing  > ratioOftrials * # possbile act, then set numOfIte = ratioOftrials * # possbile act
	// meaning that by estimation, we only wanna see a certain ratio of all actions
	//otherwise it is wasting time
	//how many updates to make to do the estimate
	Double ratioOfTrials = 0.3;
	//try certain number of updates
	final int tryUpdates = 5;
	//try seeing certain number of actions
	 int trySeeing = 5;
	//the depth of variables that we reach
	//this is dynamic
	long t0 = 0;
	//final int iterationTime = 10;
	
	//if time out
	boolean stopAlgorithm = false;
	
	//base number of dived the alpha legal region
	int AlphaTime = 10;
	//if record the tree
	final boolean ifRecord = false;
	//oldQ * this = ConvergeT
	final double RelativeErr = 0.01;

	//max time of iteratively shrink alpha
	final int MaxShrink = 5;
	//when we go beyond legal region, do we project back by
	//decreasing the same value for all vars or by times a factor
	final boolean ifProjectwtTime = false;
	
	final boolean ifPrint = false;
	final boolean ifPrintEst = false;
	final boolean ifPrintBit = false;
	boolean ifPrintInitial = false;
	final boolean ifPrintProb = false;
	//print out the starting and ending points of each random restart
	final boolean ifPrintGrid = false;
	final boolean ifDefaultNoop = true;
	
	//print trajectory actions step by step in the end
	final boolean ifPrintTraje = false;
	
	//print the routine updates
	final boolean ifPrintUpdateInRoutine = false;
	
	// if we already go over this depth, we use calculation rather than real estimate
	final int MaxEstimateDepth = 10;
	
	//if use forward accumulation or reverse accumulation
	final boolean ifReverseAccu = true;
	final double fixAlpha = -1;
	final boolean ifRecordRoutine = true;
	final boolean ifTopoSort = true;

	int maxDepth = 0;
	
	//stats
	double roundRandom = 0;
	double roundUpdates = 0;
	double roundSeen = 0;
	long sizeOfNonLeaf = 0;
	
	ArrayList<Double> bestNumAct = new ArrayList<Double>();
	double highestScore = -Double.MAX_VALUE;
	HashMap<ArrayList<Double>, Double> routine = new HashMap<ArrayList<Double>, Double>();
	HashMap<ArrayList<Double>, Double> initActRoutine = new HashMap<ArrayList<Double>, Double>();
	//ArrayList<ArrayList<Double>> triedAct = new ArrayList<ArrayList<Double>>();
	
	//a table transfers from actions to numbers
	//HashMap<Integer, HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, Integer>>> trans2Num = new HashMap<Integer, HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Integer>>>();
	HashMap<Integer, HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, TreeExp>>> trans2Tree = new HashMap<Integer, HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,TreeExp>>>();
	ArrayList<PVAR_NAME> int2PVAR = new ArrayList<>();
	ArrayList<ArrayList<TYPE_NAME>> int2TYPE_NAME = new ArrayList<>();
	ArrayList<ArrayList<LCONST>> int2LCONST = new ArrayList<>();
	
	
	//build the reward expectation function
	// with only the root level actions as variable
	// the other levels actions are treated as constant
	
	//record if there is any action variable not in the graph
	//would eventually set them to be false
	
	
	/**********************
	 * following code is for debuging use
	 * make sure all flags are set to be false before real run
	 * @param s
	 */
	//used to fix the move-left action to be true
	//domain: crossing_1
	public final boolean ifFixMoveLeft = false;
	
	
	public void OrderTypes(TEState s){
		Iterator thisIterator = s._hmTypes.entrySet().iterator(); 
		while (thisIterator.hasNext()) { 
		    Map.Entry entry = (Map.Entry) thisIterator.next();     
		    OBJECT_TYPE_DEF val = (OBJECT_TYPE_DEF)entry.getValue(); 
		    if(val._typeSuperclass != null){
		    	TYPE_NAME theSuper = val._typeSuperclass;
		    	if(!superClass.containsKey(val._sName)){
		    		superClass.put(val._sName, new ArrayList<>());
		    	}
		    	superClass.get(val._sName).add(theSuper);
		    	if(!childClass.containsKey(theSuper)){
		    		childClass.put(theSuper, new ArrayList<>());
		    	}
		    	childClass.get(theSuper).add(val._sName);
		    }
		}
	}
	
	TreeExp BuildF(State s) throws Exception {
		
		INSTANCE instance = _rddl._tmInstanceNodes.get(_sInstanceName);
		double cur_discount = 1;
		
		// Q function
		TreeExp F = new TreeExp(0.0, null);

		// initialize
		//record action nodes
		int actionCounter = 0;
		boolean ifAddIntTrans = int2PVAR.size() == 0;
		for(int h = 0; h < maxVarDepth; h ++) {
			trans2Tree.put(h, new HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, TreeExp>>());
			for (PVAR_NAME p : s._alActionNames) {
				trans2Tree.get(h).put(p, new HashMap<ArrayList<LCONST>, TreeExp>());
				ArrayList<ArrayList<LCONST>> terms = s.generateAtoms(p);
				//find list of types of the p_var_name
				PVARIABLE_DEF pvar_def = s._hmPVariables.get(p);
				//list of type names of the pvar
				ArrayList<TYPE_NAME> theTypeNames = pvar_def._alParamTypes;
				for (ArrayList<LCONST> t : terms) {
					trans2Tree.get(h).get(p).put(t, new TreeExp((Integer)actionCounter, null));
					//trans2Num.get(h).get(p).put(t, actionCounter);
					
					//add the var name and type names to associate with the number
					if(ifAddIntTrans) {
						int2PVAR.add(p);
						int2TYPE_NAME.add(theTypeNames);
						minimalProb.add(-Double.MAX_VALUE);
					}
					
					if(h == 0) {
						if(!act2Int.containsKey(p)) {
							act2Int.put(p, new HashMap<>());
						}
						act2Int.get(p).put(t, actionCounter);
					}
					actionCounter ++;
				}
			}
		}
		
		//initialize and copy states for trajcotry
		TEState as = new TEState();
		State cs = new State();
		cs = (State)DeepCloneUtil.deepClone(s);
		as.init(cs);
		
		//calculate concurrency
		if (ifConstructConstraints) {
			System.out.println("Rebuild constraints system!!!!");
			sumVars = new ArrayList<>();
			sumLimits = new ArrayList<>();
			sumLimitsExpr = new ArrayList<>();
			sumCoeffecients = new ArrayList<>();
			ifInSumConstraints = new Boolean[countActBits];
			Arrays.fill(ifInSumConstraints, false);
			try {
				as.AddExtraActionEff(trans2Tree.get(0), sumVars, sumLimits, sumLimitsExpr, sumCoeffecients);
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				System.exit(0);
			}
			GetRandomTrajAct(as);
			ifConstructConstraints = false;
		}
		
		//deal with hard constraints
		
		int countBase = 0;
		for (PVAR_NAME p : s._alActionNames) {
			ArrayList<ArrayList<LCONST>> ts = s.generateAtoms(p);
			if (Policy._extraEffects.containsKey(p)) {
				// addVars.addAll(c)
				ArrayList<TYPE_NAME> typenames = s._hmPVariables.get(p)._alParamTypes;
				HashMap<ArrayList<TYPE_NAME>, ArrayList<BOOL_EXPR>> possibleMaches = Policy._extraEffects.get(p);
				Iterator it = possibleMaches.entrySet().iterator();
				// first figure out which are the variables used in for this PVAR_NAME
				while (it.hasNext()) {
					Map.Entry pair = (Map.Entry) it.next();
					// first decide if the type of each parameter is a subclass of the type of
					// parameters in the preconditions
					ArrayList<TYPE_NAME> constraintsTypeName = (ArrayList<RDDL.TYPE_NAME>) pair.getKey();

					if (TEState.IfSuperClassList(typenames, constraintsTypeName)) {
						int countIndex = 0;
						for (ArrayList<LCONST> t : ts) {

							// times each additional effects to the action variables
							for (BOOL_EXPR theAddEff : (ArrayList<BOOL_EXPR>) pair.getValue()) {
								RandomDataGenerator newR = new RandomDataGenerator();
								// laod the substituion of lvars into newsub
								// pass new sub to the sampling of the constraints
								HashMap<LVAR, LCONST> newSubs = new HashMap<>();
								// deal with each parameter appeared in the precondition
								for (int i = 0; i < Policy._extraEffectsLVARS.get(p).get(constraintsTypeName)
										.size(); i++) {
									// important:
									// we assume that there is no repetition of types in both the preconditions and
									// action variable subs
									LVAR theVar = (LVAR) Policy._extraEffectsLVARS.get(p).get(constraintsTypeName)
											.get(i);
									newSubs.put(theVar, t.get(i));
								}
								if(newSubs.size() == 1 && theAddEff instanceof PVAR_EXPR && ((PVAR_EXPR)theAddEff)._alTerms.size() == 1) {
									Map.Entry<LVAR, LCONST> entry = newSubs.entrySet().iterator().next();
									LVAR key = entry.getKey();
									if(!key.toString().equals(((PVAR_EXPR)theAddEff)._alTerms.get(0).toString())) {
										LCONST value = entry.getValue();
										newSubs.put((LVAR)((PVAR_EXPR)theAddEff)._alTerms.get(0), value);
									}
									
								}
								TreeExp theT = TEState.toTExp(theAddEff.sample(newSubs, s, newR), null);
								if (theT.Is0()) {
									Policy.ifForcednotChoose[countBase + countIndex] = true;
									break;
								}
							}
							countIndex ++;
						}
					}
				}
				
			}
			countBase += ts.size();
		}
		
		//for(Boolean b: Policy.ifForcednotChoose){
		//	System.out.print(b + " ");
		//}
		//System.out.println();
		
		//build the super-child relations between all types in this instances
		//only do it once in each instances
		if(superClass.isEmpty()){
			System.out.println("Rebuild super classes!!!!");
			OrderTypes(as);
		}
		
		//start calclulating trajectories
		int h = 0;

		routine.clear();
		
		double updatePerNode = 0.00001;
		if(!ifFirstStep && numberNodesUpdates != 0) {
			updatePerNode = timeUsedForCal / numberNodesUpdates;
			
			System.out.println("Dealt with number of nodes times updates: " + numberNodesUpdates + " using time " + timeUsedForCal);
			System.out.println("Estimate calculation time per node per update: " + updatePerNode);
		}
		
		TreeSizeCounter treeCounter = new TreeSizeCounter();
		ArrayList<Long> counterRecord = new ArrayList<>();
		long lastStepCounter = 0;
		//estimation of number of nodes for next step
		double nextStepNodesNum = -1;
		QuadraticEstimator qEst = new QuadraticEstimator(counterRecord);
		for (; h < maxDepth; h++) {	
			Policy.stateHistory.add(as.QuickCopy());
			//if(_ifDisAction){
			//	as.CalActionDiscount();
			//}
			//actions
			ArrayList<PVAR_INST_DEF> trajeActs = new ArrayList<RDDL.PVAR_INST_DEF>();
			
			if(h < maxVarDepth){
				for (PVAR_NAME p : as._alActionNames) {
					for (ArrayList<LCONST> t : as.generateAtoms(p)) {
						HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, TreeExp>> in1 = trans2Tree.get(h);
						HashMap<ArrayList<LCONST>, TreeExp> in2 = in1.get(p);
						TreeExp tr = in2.get(t);
						PVAR_INST_DEF theAct = new PVAR_INST_DEF(p._sPVarName,
								(Object) tr, t);
						trajeActs.add(theAct);
					}
				}
			}
			else{
				int index = 0;
				for (PVAR_NAME p : as._alActionNames) {
					for (ArrayList<LCONST> t : as.generateAtoms(p)) {
						int realIndex = -1;
						for(int c = 0; c < sumVars.size(); c ++) {
							if(sumVars.get(c).contains(index)) {
								realIndex = c;
							}
						}
						if(realIndex == -1) {
							trajeActs.add(new PVAR_INST_DEF(p._sPVarName,
									(Object)new TreeExp(0.5, null), t));
						}
						else {
							trajeActs.add(new PVAR_INST_DEF(p._sPVarName,
									(Object)new TreeExp((Double)randomAction.get(realIndex), null), t));
						}
						index ++;
					}
				}
			}
			as.SetActNoCompute(trajeActs);
			


			cur_discount *= instance._dDiscount;
			// output the current achieved depth
			if(ifPrint){
				System.out.println("finish: " + (h+1)+ " steps.");
			}
			
			//try three times of update
			if(searchDepth == -1){
				long numOfNodes = treeCounter.nonLeafCounter;
				// System.out.println("try: " + numOfNodes);
				long timeLeft = _timeAllowed - (System.currentTimeMillis() - t0);
				// System.out.println("time left: " + timeLeft);
				if(F.counter != 0) {
					if (!ifFirstStep) {
						//possibly maxvardepth is bigger than the searchdepth being used
						int currentRealConformant = maxVarDepth > h ? h : maxVarDepth; 
						
						if ((numOfNodes + nextStepNodesNum) * updatePerNode * 500 > timeLeft) {
							System.out.println("predict next size: " + nextStepNodesNum);
							System.out.println("Total size: " + (numOfNodes + nextStepNodesNum));
							System.out.println("use conformant depth: " + currentRealConformant);
							System.out.print("Time left: " + timeLeft);
							h++;
							break;
						}
					} else {
						if (timeLeft < _timeAllowed * 0.3) {
							h++;
							System.out.println("Estimating update time built to depth = " + h);
							break;
						}
					}
				}
				
			}
			  
			//System.out.println("h: " + h);
			if(h!=maxDepth - 1){
				as.computeNextState(_random);
				TreeExp reward = TEState.toTExp(as._reward.sample(new HashMap<LVAR, LCONST>(), as, _random), null);
				//System.out.println(as);
				//System.out.println("reward: " + reward);
				F = (TreeExp)RDDL.ComputeArithmeticResult(F, RDDL.ComputeArithmeticResult(reward, cur_discount, "*"), "+");
				treeCounter.Count(F);
				F.counter = treeCounter.nonLeafCounter;
				long thisStepNumNodes = F.counter - lastStepCounter;
				if(ifPrintSizePredict) {
					System.out.println(thisStepNumNodes + " " + nextStepNodesNum);
				}
				
				counterRecord.add(thisStepNumNodes);
				
				//print out the real num of nodes and prediction (from last step) num of nodes
				//System.out.println(thisStepNumNodes + " " + nextStepNodesNum);
				//update prediction for next step
				nextStepNodesNum = qEst.PredictNextSize();
				//record this step
				lastStepCounter = F.counter;
				as.advanceNextState();
				//System.out.println(h);
				//System.out.println(as);
			}
			
			// check time
			if ((System.currentTimeMillis() - t0) > _timeAllowed) {
				h ++;
				System.out.println("Forced to stop building tree!");
				break;
			}
		}

		if(currentRound < 5 && !ifFirstStep)
		_visCounter.depthInTotal += h;
		
			System.out.println(h);
			System.out.println("finish: " + (h+1) + " steps.");
		
		//double check that maxvardepth is at most same as h
		if(maxVarDepth > h){
			maxVarDepth = h;
		}
		
		if(ifPrint)
		System.out.println("We are finally using " + maxVarDepth + "-layer variables");
		
		//record the maxvardepth used temporarily
		//later in update step decide if add this to statistics
		//based on if having useful updates
		tmpVarDepthChange = maxVarDepth;
		tmpSearchDepthChange = maxDepth;
		
		System.out.println("buildf counter size: " + F.counter);
		return F;
	}
	//arbitarily search over legal region of alpha
	//use the best step length
	public double FndAlpha(State s, TreeExp F, ArrayList<Double> actionProb, ArrayList<Double> delta) throws EvalException{
		double maxAlpha = Double.MAX_VALUE;
		//we allow actionprob to go beyond 1
		//so first find the max prob and then acrrordingly find the space
		double maxProb = -1;
		for(double a: actionProb){
			if(a > maxProb){
				maxProb = a;
			}
		}
		maxProb += 1;
		//traverse each bit to shrink maxalpha
		for(int i = 0; i < actionProb.size(); i ++){
			double possibleAlpha = -1;
			if(delta.get(i) > 0){
				possibleAlpha = (maxProb-actionProb.get(i)) / Math.abs(delta.get(i));
			}
			if(delta.get(i) < 0){
				possibleAlpha = (actionProb.get(i) - (-1)) / Math.abs(delta.get(i));
			}
			if(possibleAlpha != -1 && possibleAlpha < maxAlpha){
				
				maxAlpha = possibleAlpha;
			}
		}
		//if we do concurrency projection then we need to again shrink the alpha by constraint the sum of prob be no bigger than
		//concurrency
		//System.out.println("max alpha is: " + maxAlpha);
		//now try alpha from 0 to maxAlpha
		double bestAlpha = 0;
		double bestQ = Double.NEGATIVE_INFINITY;
		ArrayList<Double> tempActProb = new ArrayList<Double>();
		for(int i = 0; i < actionProb.size(); i ++){
			tempActProb.add(0.0);
		}
		ArrayList<Double> bestActProb = new ArrayList<Double>();
		
		for(int i = 0; i < actionProb.size(); i ++){
			
			bestActProb.add(0.0);
		}
		
		// try to find the alpha with highest Q
		double realBest = -1;
		//double realNeeded = -1;
		
		// this is a loop to find smallest alpha because too large alpha could
		// be a problem
		// if we find in one iteration alpha is chosen to be the smallest among
		// possible then we extend another "alphatime"
		// between 0 and the smallest
		// maxAlpha = 0.2;
		int shrinkCounter = 0;
		double realNorm = 0;
		while (true) {
			if (fixAlpha == -1)
				bestAlpha = 0;
			else {
				bestAlpha = fixAlpha;
				AlphaTime = 1;
			}

			for (int i = 1; i <= AlphaTime; i++) {
				
				if (fixAlpha == -1){
					bestAlpha += maxAlpha / AlphaTime;
				}
				// System.out.println(bestAlpha);
				// update temp actprob
				
				for (int j = 0; j < actionProb.size(); j++) {
					double d = delta.get(j);
					double update = bestAlpha * d;
					double now = actionProb.get(j);
					
					if(now + update < 0){
						update = -now;
					}
					if(now + update > 1){
						update = 1 - now;
					}
					//norm += update * update;
					double newVal = now + update;

					tempActProb.set(j, newVal);
				}
				//norm = Math.sqrt(norm/actionProb.size());
				try {
					Projection(tempActProb);
				} catch (Exception e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}

				// update bestQ
				HashMap<TreeExp, Double> valRec = new HashMap<TreeExp, Double>();
				try {

					double theQ = F.RealValue(tempActProb, valRec);
					if (theQ > bestQ) {
						bestQ = theQ;
						// update actionProb
						for (int j = 0; j < actionProb.size(); j++) {
							bestActProb.set(j, tempActProb.get(j));
						}
						realBest = bestAlpha;
						double norm = 0;
						for(int j = 0; j < actionProb.size(); j ++){
							double diff = tempActProb.get(j) - actionProb.get(j);
							norm += diff * diff;
						}
						norm = Math.sqrt(norm / actionProb.size());
						realNorm = norm;
					}
				} catch (EvalException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}

			// System.out.println("BestAlpha is :" + realBest);

			if (fixAlpha == -1 && realBest == maxAlpha / AlphaTime) {
				maxAlpha /= AlphaTime;
				shrinkCounter++;
				
				if (shrinkCounter > MaxShrink) {
					break;
				}
				// System.out.println("Alpha is too large, will try alpha between 0 and "
				// + maxAlpha );
			} else {
				break;
			}
		}
		
		if(convergeNorm != -1 && realNorm <= convergeNorm){
			ifConverge = true;
		}

		for (int j = 0; j < actionProb.size(); j++) {
			actionProb.set(j, bestActProb.get(j));
		}
		return bestQ;
	}
	
	public void Projection(ArrayList<Double> actionProb) throws Exception {
		
		// first masking actions that are not in the graph
		MaskingActions(actionProb);
		for (int h = 0; h < maxVarDepth; h++) {
			//set minimal prob of each var in this step to -1
			int base = h * countActBits;
			for(int i = 0; i < countActBits; i ++) {
				minimalProb.set(base + i, -Double.MAX_VALUE);
			}
			//value record for each node
			//so long as this is in the same depth
			//the value record could be reused
			HashMap<LVAR, LCONST> valMap = new HashMap();
			//traverse each action var to see if any has forced condition
			//also find the highest marginal action variable in the exist force action
			int highestMarIndex = -1;
			double highestMar = -1.0;
			PVAR_NAME highestName = null;
			ArrayList<TYPE_NAME> highestTypeName = null;
			for(int i = 0; i < countActBits; i ++) {
				int j = i + base;
				PVAR_NAME theP = int2PVAR.get(j);
				if(_forceActionCondForall.containsKey(theP)) {
					ArrayList<TYPE_NAME> typenames = int2TYPE_NAME.get(j);
					HashMap<ArrayList<TYPE_NAME>, ArrayList<BOOL_EXPR>> possibleMaches = 
							Policy._forceActionCondForall.get(theP);
					Iterator it = possibleMaches.entrySet().iterator();
					//traverse and find each cond associated with it
				    while (it.hasNext()) {
				        Map.Entry pair = (Map.Entry)it.next();
				        //first decide if the type of each parameter is a subclass of the type of parameters in the preconditions
				        ArrayList<TYPE_NAME> constraintsTypeName = (ArrayList<RDDL.TYPE_NAME>)pair.getKey();
				        if(TEState.IfSuperClassList(typenames, constraintsTypeName)) {
				        	//traverse each cond
				        	for (BOOL_EXPR theforceCond : (ArrayList<BOOL_EXPR>)pair.getValue()) {
								RandomDataGenerator newR = new RandomDataGenerator();
								Object theCondVal = null;
								try {
									theCondVal = theforceCond.sample(valMap, stateHistory.get(h), newR);
									double theCondDouble = -1;
									if(theCondVal instanceof Double) {
										theCondDouble = (Double)theCondVal;
									}
									else {
										theCondDouble = ((TreeExp)theCondVal).RealValue(actionProb, new HashMap<>());
									}
									
									if(theCondDouble > 1 || theCondDouble < 0) {
										throw new Exception("value of forcing action condition can only be within 0 ~ 1!");
									}
									if(!(h == 0 && ifForcednotChoose[i]) && theCondDouble > minimalProb.get(j)) {
										minimalProb.set(j, theCondDouble);
									}
								} catch (EvalException e) {
									// TODO Auto-generated catch block
									e.printStackTrace();
								}
							}
				        }
				    }
				}
				//traverse each action variable to check exsits force action
				//find the one with highest marginals
				if(_forceActionCondExist.containsKey(theP)) {
					ArrayList<TYPE_NAME> typenames = int2TYPE_NAME.get(j);
					HashMap<ArrayList<TYPE_NAME>, ArrayList<Object>> possibleMaches = 
							Policy._forceActionCondExist.get(theP);
					Iterator it = possibleMaches.entrySet().iterator();
					//traverse and find each cond associated with it
				    while (it.hasNext()) {
				        Map.Entry pair = (Map.Entry)it.next();
				        //first decide if the type of each parameter is a subclass of the type of parameters in the preconditions
				        ArrayList<TYPE_NAME> constraintsTypeName = (ArrayList<RDDL.TYPE_NAME>)pair.getKey();

				        if(TEState.IfSuperClassList(typenames, constraintsTypeName)) {
				        	boolean ifIgnor = false;
				        	if(h == 0 && Policy.ifForcednotChoose[j]) {
				        		ifIgnor = true;
				        	}
				        	if( !ifIgnor && actionProb.get(j) > highestMar) {
				        		highestMar = actionProb.get(j);
				        		highestMarIndex = j;
				        		highestName = theP;
				        		highestTypeName = constraintsTypeName;
				        	}
				        }
				    }
				}
			}
			
			//deal with the exist force action
			//only deal with the highest marginal variable
			//traverse each cond
			if(highestMarIndex != -1) {
				for (Object theforceCond : (ArrayList<Object>)_forceActionCondExist.get(highestName).get(highestTypeName)) {
					RandomDataGenerator newR = new RandomDataGenerator();
					Object theCondVal = null;
					try {
						if(theforceCond instanceof BOOL_EXPR) {
							theCondVal = ((BOOL_EXPR)theforceCond).sample(valMap, stateHistory.get(h), newR);
						}
						if(theforceCond instanceof Double) {
							theCondVal = theforceCond;
						}
						double theCondDouble = -1;
						if(theCondVal instanceof Double) {
							theCondDouble = (Double)theCondVal;
						}
						else {
							theCondDouble = ((TreeExp)theCondVal).RealValue(actionProb, new HashMap<>());
						}
						
						if(theCondDouble > 1 || theCondDouble < 0) {
							throw new Exception("value of forcing action condition can only be within 0 ~ 1!");
						}
						if(theCondDouble > minimalProb.get(highestMarIndex)) {
							minimalProb.set(highestMarIndex, theCondDouble);
						}
					} catch (EvalException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}
			}
        	//System.out.println(minimalProb);
        	//set everything 
			for(int j = 0 ; j < countActBits; j ++) {
				if(minimalProb.get(base + j) > 0) {
					actionProb.set(base + j, minimalProb.get(base + j));
				}
				if(h == 0 && ifForcednotChoose[j]) {
					actionProb.set(j, 0.0);
				}
			}
			
			for (int c = 0; c < sumVars.size(); c++) {
				int concurrency = -1;
				if(sumLimitsExpr.get(c) == null) {
					concurrency = sumLimits.get(c);
				}
				else {
					TreeExp treeRes = (TreeExp)sumLimitsExpr.get(c).sample(new HashMap<>(), stateHistory.get(h), _random);
					if(treeRes.term != null && treeRes.term.var == -1) {
						concurrency = (int) Math.round(treeRes.ToNumber());
					}
					else {
						concurrency = (int)((TreeExp)treeRes).RealValue(actionProb, new HashMap<>());
					}
				}
				ArrayList<Integer> morethan1Counter = new ArrayList<Integer>();
				int numOfVar = sumVars.get(c).size();

				// calculate the sum of probs, max probs, more than 1 counter
				// for each variable depth
				for (int j = 0; j < maxVarDepth; j++) {
					morethan1Counter.add(0);
				}

				ArrayList<Double> sumOfProb = new ArrayList<Double>();
				for (int j = 0; j < maxVarDepth; j++) {
					sumOfProb.add(0.0);
				}

				ArrayList<Double> maxOfProb = new ArrayList<Double>();
				for (int j = 0; j < maxVarDepth; j++) {
					maxOfProb.add(Double.NEGATIVE_INFINITY);
				}
				for (int k = 0; k < numOfVar; k++) {
					
					int j = sumVars.get(c).get(k) + h * countActBits;

					int currentDepth = h;
					double newVal = actionProb.get(j);
					if (newVal > 1) {
						morethan1Counter.set(currentDepth, morethan1Counter.get(currentDepth) + 1);
					}
					// update sum to do projection

					sumOfProb.set(currentDepth, sumOfProb.get(currentDepth) + newVal * sumCoeffecients.get(c).get(k));
					if (newVal > maxOfProb.get(currentDepth)) {
						maxOfProb.set(currentDepth, newVal);
					}
				}

				// do projection for this step
				double sumP = sumOfProb.get(h);
				double adjustPar = Double.NaN;
				if (sumP > concurrency) {
					adjustPar = sumP - concurrency;
					double theRemain = adjustPar;
					int notZero = 0;
					for (int k = 0; k < numOfVar; k++) {
						int j = sumVars.get(c).get(k);
						int index = base + j;
						double theVal = actionProb.get(index);
						if (theVal > 0 && theVal != minimalProb.get(index)) {
							notZero += sumCoeffecients.get(c).get(k);
						}
					}
					while (theRemain > 0) {
						double del = theRemain / notZero;
						theRemain = 0;
						notZero = 0;
						for (int k = 0; k < numOfVar; k++) {
							int j = sumVars.get(c).get(k);
							int theCoe = sumCoeffecients.get(c).get(k);
							int index = base + j;
							double oldVal = actionProb.get(index);
							if (oldVal == 0 || oldVal == minimalProb.get(index)) {
								continue;
							}
							double newVal = oldVal - del;
							// if newVal < minimalProb
							// set back newVal to minimalProb
							// add back to remin
							if(minimalProb.get(index) > 0 && newVal < minimalProb.get(index)) {
								actionProb.set(index, minimalProb.get(index));
								theRemain += (minimalProb.get(index) - newVal) * theCoe;
							}
							else {
								if(newVal < 0) {
									actionProb.set(index, 0.0);
									theRemain += (0.0 - newVal) * theCoe;
								}
								else {
									actionProb.set(index, newVal);
								}
							}
							if (actionProb.get(index) > 0) {
								notZero += theCoe;
							}
						}
					}
				}
			}
			//deal with sums
			for(int i = 0; i < sumVars.size(); i ++) {
				if(ifEqual.get(i)) {
					double sumH = 0;
					int countInGraph = 0;
					for(int j = 0; j < sumVars.get(i).size(); j ++) {
						int thecoe = sumCoeffecients.get(i).get(j);
						int index = sumVars.get(i).get(j) + base;
						if(ifInSumConstraints[index - base] && !ifForcednotChoose[index - base]) {
							sumH += actionProb.get(index) * thecoe;
							countInGraph += thecoe;
						}
					}
					int concurrency = -1;
					if(sumLimitsExpr.get(i) == null) {
						concurrency = sumLimits.get(i);
					}
					else {
						concurrency = (int)sumLimitsExpr.get(i).sample(new HashMap<>(), stateHistory.get(h), _random);
					}
					double diff = concurrency - sumH;
					double addToBit = diff / countInGraph;
					for(int j = 0; j < sumVars.get(i).size(); j ++) {
						int index = sumVars.get(i).get(j) + base;
						if(ifInSumConstraints[index - base] && !ifForcednotChoose[index - base]) {
							double old = actionProb.get(index);
							actionProb.set(index, old + addToBit);
						}
					}
				}
			}
		}
	}
	
	//This must be called in the beginning of a projection
	public void MaskingActions(ArrayList<Double> actions) {
		for(int i = 0; i < actions.size(); i ++) {
			if(!ifInGraph[i]) {
				actions.set(i, 0.0);
			}
		}	
	}

	public ArrayList<Double> UpdateAllwtProj(State s, TreeExp F) throws EvalException{

		tmpUpdatesChange = 0;
		
		ArrayList<Double> actionProb = new ArrayList<Double>();
		for(int i = 0; i < countActBits * maxVarDepth; i ++){
			actionProb.add(0.0);
		} 
		
		//ArrayList<TExp> visited = new ArrayList<TExp>();
		//int b = F.Size(visited );
		//iteration counter
		int randomRestart = 0;
		roundRandom = 0;
		roundUpdates = 0;
		roundSeen = 0;
		
		//Record the best actionProb that gets the highest Q value in F tree
		ArrayList<Double> bestActionProb = new ArrayList<Double>();
		for(int i = 0; i < countActBits; i ++){
			bestActionProb.add(0.0);
		}
		double bestQ = Double.NEGATIVE_INFINITY;
		ArrayList<Double> completeBest = new ArrayList<Double>();
		for(int i = 0; i < countActBits * maxVarDepth; i ++){
			completeBest.add(0.0);
		}
		//generate concrete actions for getting the starting point of rrs

		//topological ordering, record two things
		//1. number of non-leaf nodes
		//2. action variables in the graph (ifIngraph[])
		ArrayList<TreeExp> que = new ArrayList<TreeExp>();
		if(ifReverseAccu){
			que = F.TopologQueue(ifTopoSort);
			if(currentRound < 5 && !ifFirstStep){
				_visCounter.sizeInTotal += F.numOfNonLeaf;

			}
			//System.out.println("Number of non-leaf nodes: " + F.numOfNonLeaf);
			//System.out.print("Action variables in graph: ");
			//for(int i = 0; i < ifInGraph.length - 1; i ++) {
			//	System.out.print(ifInGraph[i] + ", ");
			//}
			//System.out.println(ifInGraph[ifInGraph.length - 1]);
		}
		
		stopAlgorithm = false;
		//looping over rando restarts
		while(!stopAlgorithm){

			//flag for convergence
			ifConverge = false;
			
			//updates that being done in this random restart
			//note that these updates may not be all used in statistics
			double updatedasCounter = 0;

			//initialize the action bits to 0 and 1 randomly
			for (int i = 0; i < actionProb.size(); i++) {
				actionProb.set(i, _random.nextUniform(0, 1.0));
			}
			
			try {
				Projection(actionProb);
			} catch (Exception e2) {
				// TODO Auto-generated catch block
				e2.printStackTrace();
			}


			//evaluate the initial action bits
			try {
				Projection(actionProb);
			} catch (Exception e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
			HashMap<TreeExp, Double> valRec = new HashMap<TreeExp, Double>();
			HashMap<TreeExp, Double> gradRec = new HashMap<TreeExp, Double>();
			//initialize oldQ to be realvalue calculated with initial action prob
			double oldQ = F.RealValue(actionProb, valRec);
			
			if(ifRecordRoutine){
				UpdateRoutine(F, s, actionProb, true);
			}
			
			//this is used to judge whether Q has been changed
			double initialQ = oldQ;
			if(ifPrintInitial){
				System.out.println(actionProb + " " + initialQ);
			}
			if(ifPrint){
				System.out.println("Q is initlaized to: " + oldQ);
			}
			
			//update bestQ and action
			if(oldQ > bestQ){
				bestQ = oldQ;
				for(int a = 0; a < countActBits; a ++){
					bestActionProb.set(a, actionProb.get(a));
				}
				for(int a = 0; a < actionProb.size(); a ++){
					completeBest.set(a, actionProb.get(a));
				}
			}
			
			//dead bit record
			//if during this random restart, certain bits never change, it means that Q is not related to it
			//set it to be 0
			//only for top level 
			ArrayList<Boolean> ifthisBitChange = new ArrayList<Boolean>();
			for(int a = 0; a < actionProb.size(); a ++){
				ifthisBitChange.add(false);
			}
			if(ifPrintBit){
				System.out.println();
				for(int a = 0; a < actionProb.size(); a++){
					System.out.println("a for " + "v" + a + " " + actionProb.get(a));
				}
				System.out.println();
			}
			//initialize newQ
			double newQ = 0; // this will be recalculated later
			
			//one random restart
			//quit when either ifconverge = true (this is udpated in fndalpha)
			//or running out of time
			while(!ifConverge && !stopAlgorithm){

				//calculate delta
				ArrayList<Double> delta = new ArrayList<Double>();
				try {
					F.RevAccGradient(ifTopoSort, que, delta, actionProb);
				} catch (Exception e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				
				if(ifFixMoveLeft) {
					for(int i = 0; i < 9; i ++) {
						delta.set(i, 0.0);
					}
				}
				
				//do updates for each bit
				if (ifPrintBit) {
					for (int i = 0; i < actionProb.size(); i++) {
						System.out.println("d for " + "v" + i + " " + delta.get(i));
					}
				}
				//record if a bit is changed
				for (int i = 0; i < delta.size(); i++) {
					double d = delta.get(i);
					if (d != 0) {
						ifthisBitChange.set(i, true);
					}
				}

				updatedasCounter ++;
				//this step updates prob and return the Q
				newQ = FndAlpha(s, F, actionProb, delta);
				//System.out.println(routine.size());
				if(ifRecordRoutine){
					UpdateRoutine(F, s, actionProb, true);
				}

				if(ifPrintBit){
					for(int a = 0; a < actionProb.size(); a++){
						System.out.println("a for " + "v" + a + " " + actionProb.get(a));
					}
				}
				
				//now alphas are changed so we need to clear the value record in the tree
				valRec.clear();

				if(ifPrint){
					System.out.println("oldQ: " + oldQ + "\n");
					System.out.println("newQ: " + newQ + "\n");
				}

				oldQ = newQ;
				//we don't need to clear valrec again
				//because the value when calculating newQ can be reused in next iteration
				if(System.currentTimeMillis() - t0 > _timeAllowed * 0.95){
					stopAlgorithm = true;
					break;
				}
			}
			
			//converged; continue to next random restart
			//record statics only if the Q value has been changed during the updates
			if(newQ != initialQ){
				roundRandom ++;
				roundUpdates += updatedasCounter;
				updatesIntotal += updatedasCounter;
				if(currentRound < 5 && !ifFirstStep){
					_visCounter.updatesInTotal += updatedasCounter;
					_visCounter.randomInTotal ++;
				}
				tmpUpdatesChange += updatedasCounter;
			}
			if(ifPrint){
				if(ifConverge){
					System.out.println("RR: " + randomRestart + "converged!");
				}
				else{
					System.out.println("RR: " + randomRestart + "forced to stop because running out of time.");
				}
			}
			//Get the Q value for this convergence
			if(newQ > bestQ){
				if(ifPrint){
					System.out.println("Previous best is: " + bestQ + " and now the Q is: " + newQ);
				}
				
				bestQ = newQ;
				for(int a = 0; a < countActBits; a ++){
					bestActionProb.set(a, actionProb.get(a));
				}
				for(int a = 0; a < actionProb.size(); a ++){
					completeBest.set(a, actionProb.get(a));
				}
				
				//if an action bit is not changed
				//set it to be false
				if(ifDefaultNoop){
					for (int a = 0; a < countActBits; a++) {
						if (!ifthisBitChange.get(a)) {
							bestActionProb.set(a, 0.0);
						}
					}
				}
			}
			else{
				if(ifPrint){
					System.out.println("Failed to update Q. Previous best is: " + bestQ + " and now the Q is: " + newQ); 
				}		
			}
			
			if(ifDefaultNoop){
				//System.out.println(ifthisBitChange);
				for (int a = 0; a < countActBits; a++) {
					//System.out.println(ifthisBitChange);
					if (!ifthisBitChange.get(a)) {
						bestActionProb.set(a, 0.0);
					}
				}
			}
		}
		/*
		if(roundRandom == 0){
			_visCounter.updateTime --;
			_visCounter.SeenTime --;
		}
		*/
		if(ifPrintGrid){
			System.out.println("In total: " + randomRestart);
		}
		//record how many random restart have been done
		String countingStr = new String();
		countingStr += "\n\n*************************\n"
				     + "\n******** Summary ********\n"
				     + "\n*************************\n";
		countingStr += "Number of Random Restart: " + roundRandom + "\n";
		countingStr += "Number of Updates: " + roundUpdates + "\n";
		countingStr += "Number of Actions Seen: " + roundSeen + "\n";
		System.out.println(countingStr);
		
		//printout the action probs
		if(ifPrintBit){
			System.out.println("\nfinal action prob: ");
			for(double a: bestActionProb){
				System.out.println(a);
			}
		}
		
		System.out.println("best: " + bestQ);
		
		if(tmpUpdatesChange != 0){
			avgUpdates += tmpUpdatesChange;
			avgSearchDepth += tmpSearchDepthChange;
			//System.out.println("add " + tmpUpdatesChange + ", get " + avgUpdates);
			avgVarDepth += tmpVarDepthChange;
			effectiveSteps ++;
			//System.out.println(tmpVarDepthChange + " " + tmpSearchDepthChange);
			//System.out.println("effective: " + effectiveSteps);
		}
		

		//System.out.println(completeBest);
		//reset the max var depth
		//according to the current ratio setup
		//maxVarDepth = new Double(searchDepth * theRatio).intValue();
		return bestActionProb; 
	}
	
	public ArrayList<Double> SampleNumAct(ArrayList<Double> varVal, State s) throws EvalException{
		int size = varVal.size();

		
		//find best action level wise
		//if use conformant, then do this for all trajectory level
		//otherwise only do this for first step
		int conformantDepth = ifConformant ? maxVarDepth : 1;

		boolean[] mute = new boolean[conformantDepth * countActBits];
		double[] res = new double[conformantDepth * countActBits]; 
		for(int h = 0; h < conformantDepth; h ++){
			ArrayList<Integer> sumForEachCons = new ArrayList<>();
			for(int c = 0; c < sumVars.size(); c ++) {
				sumForEachCons.add(0);
			}
			for(int c = 0; c < sumVars.size(); c ++) {
				int concurrency = -1;
				if(sumLimitsExpr.get(c) == null) {
					concurrency = sumLimits.get(c);
				}
				else {
					TreeExp treeRes = (TreeExp)sumLimitsExpr.get(c).sample(new HashMap<>(), stateHistory.get(h), _random);
					if(treeRes.term != null && treeRes.term.var == -1) {
						concurrency = (int) Math.round(treeRes.ToNumber());
					}
					else {
						System.out.println("Sampling result can only be a number!");
						System.exit(0);
					}
				}
				int numVar = sumVars.get(c).size();
				for(int i = 0; i < concurrency; i ++){
					double max = -Double.MAX_VALUE;
					int maxIndex = -1;
					for(int k = 0; k < numVar; k ++){
						int j = h * countActBits + sumVars.get(c).get(k);
						if(!mute[j] && varVal.get(j) > max){
							max = varVal.get(j);
							maxIndex = j;
						}
					}
					
					if(max > randomAction.get(c) || ifEqual.get(c)){
						//the new added act bit might break some concurrency
						// need to check each of them by adding a sum to it
						int initialBit = maxIndex - h * countActBits;
						Boolean ifBreak = false;
						ArrayList<Integer> backupSum = new ArrayList<>();
						for(int c2 = 0; c2 < sumVars.size(); c2 ++) {
							int concurrency2 = -1;
							if(sumLimitsExpr.get(c2) == null) {
								concurrency2 = sumLimits.get(c2);
							}
							else {
								Object objectRes = sumLimitsExpr.get(c2).sample(new HashMap<LVAR, LCONST>(), s, _random); 
								if(objectRes instanceof Double) {
									concurrency2 = (int)Math.round((Double)objectRes);
								}
								else {
									TreeExp treeRes = (TreeExp)objectRes;
									if(treeRes.term == null || treeRes.term.var != -1) {
										System.out.println("Sampling result can only be a number!");
										System.exit(0);
									}
									else {
										concurrency2 = (int)treeRes.ToNumber();
									}
								}
							}
							if(sumVars.get(c2).contains(initialBit)) {
								int theIndex = sumVars.get(c2).indexOf(initialBit);
								int theSum = sumForEachCons.get(c2) + sumCoeffecients.get(c2).get(theIndex);
								if(theSum > concurrency2) {
									ifBreak = true;
									break;
								}
								else {
									backupSum.add(theSum);
								}
							}
							else {
								backupSum.add(sumForEachCons.get(c2));
							}
						}
						if(ifBreak) {
							break;
						}
						else {
							sumForEachCons = backupSum;
							res[maxIndex] = 1;
							mute[maxIndex] = true;
						}
					}
					else{
						break;
					}
				}
				
			}
		}
		
		for(int i = 0; i < countActBits; i ++) {
			int index = i;
			if(!ifInSumConstraints[i] && varVal.get(index) > 0.5) {
				res[index] = 1;
			}
		}

		ArrayList<Double> numAct = new ArrayList<Double>();
		for(double r: res){
			numAct.add(r);
		}
		//if we are not doing conformant
		//need to add fractional actions in the future steps
		if(!ifConformant) {
			for(int j = countActBits; j < size; j ++){
				numAct.add(varVal.get(j));
			}
		}

		return numAct;
	}
	
	public void UpdateRoutine(TreeExp F, State s, ArrayList<Double> varVal, boolean ifStatistics) throws EvalException{
		//based on varVal, sample concrete action
		ArrayList<Double> closestAct = SampleNumAct(varVal, s);
		ArrayList<Double> realAct = new ArrayList<Double>();
		for(int i = 0; i < countActBits; i ++){
			realAct.add(closestAct.get(i));
		}

		//evaluate the whole action including trajectories together
		if(!routine.containsKey(closestAct)){
			double val = 0;
			HashMap<TreeExp, Double> valRec = new HashMap<TreeExp, Double>();
			val = F.RealValue(closestAct, valRec);
			routine.put(closestAct, val);
			//update highest score and the best init action
			if(val > highestScore  || bestNumAct.size() == 0){
				//System.out.println(varVal);
				//System.out.println("new best: " + val);
				highestScore = val;
				bestNumAct = closestAct;
				
				//could try to output every new update action including the trajectory
				if(ifPrintUpdateInRoutine) {
					PrintUpdateInRoutine(val, s, closestAct);
				}
			}
			//update the record for init action evaluation
			if(!initActRoutine.containsKey(realAct)) {
				initActRoutine.put(realAct, val);
				if(ifStatistics){
					roundSeen ++;
					if(currentRound < 5  && !ifFirstStep){
						_visCounter.SeenInTotal ++;
					}
				}
			}
			else {
				if(val > initActRoutine.get(realAct)) {
					initActRoutine.put(realAct, val);
				}
			}
		}
	}
	
	//sample action from largest to smallest; build actions incrementally
	public void SampleAction(State s, ArrayList<ArrayList<PVAR_INST_DEF>> conformantActs, ArrayList<Double> useNum) throws EvalException{

		
		//find the best concrete action directly
		for(int h = 0; h < maxVarDepth; h ++) {
			ArrayList<PVAR_INST_DEF> finalAction = new ArrayList<RDDL.PVAR_INST_DEF>();
			int counter = 0;
			for(PVAR_NAME p: s._alActionNames){
				for(ArrayList<LCONST> t: s.generateAtoms(p)){
					double resptNum = useNum.get(counter + h * countActBits);
					boolean ifChosen = false;
					Object actionVal = null;
					if(h == 0) {
						if(resptNum == 1.0) {
							ifChosen = true;
						}
						actionVal = true;
					}
					else {
						if(ifConformant) {
							if(resptNum == 1.0) {
								ifChosen = true;
							}
							actionVal = true;
						}
						else {
							if(resptNum > 0.0) {
								ifChosen = true;
							}
							actionVal = resptNum;
						}
					}
					if(ifChosen){
						finalAction.add(new PVAR_INST_DEF(p._sPVarName, actionVal, t));
					}
					counter ++;
				}
			}
			conformantActs.add(finalAction);
		}
	}
	

	public void GetRandomTrajAct(TEState s) throws Exception{
		//the real number of each action bit for taking random policy
		for(int c = 0; c < sumVars.size(); c ++) {
			int numVarBit = sumVars.get(c).size();
			int numVar = 0;
			for(int j = 0; j < numVarBit; j ++) {
				numVar += Policy.sumCoeffecients.get(c).get(j);
			}
			
			ArrayList<Double> comb = new ArrayList<Double>();
			Double numInTotal = 0.0;

			// caculate the number of choose k from n
			int theSumLimit = -1;
			if(sumLimitsExpr.get(c) == null) {
				theSumLimit = sumLimits.get(c);
			}
			else {
				TreeExp treeRes = (TreeExp)sumLimitsExpr.get(c).sample(new HashMap<LVAR, LCONST>(), s, _random); 
				if(treeRes.term == null || treeRes.term.var != -1) {
					System.out.println("Sampling result can only be a number!");
					System.exit(0);
				}
				else {
					theSumLimit = (int)treeRes.ToNumber();
				}
			}
			for (int k = 0; k <= theSumLimit; k++) {
				int max = numVar;
				double resu = 1;
				for (int j = 1; j <= k; j++) {
					resu *= max;
					max--;
				}
				for (int j = 2; j <= k; j++) {

					resu /= j;
				}
				// now res the is number of combs (choose j from countActBits)
				comb.add(resu);
				numInTotal += resu;
			}

			// now cal the marginal for random policy
			double marRandom = 0;
			for (int k = 1; k <= theSumLimit; k++) {
				marRandom += Double.valueOf(k) / numVar * comb.get(k)
						/ numInTotal;
			}

			randomAction.add(marRandom);
		}
		
	}
	
	//final get action algorithm
	@Override
public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
		
		double sum = 0;
		for(int i = 0; i < 46; i ++) {
			sum -= 0.7 * Math.pow(0.3, i) * 0.7 * (i + 4);
		}
		//stats
		roundRandom = 0;
		roundUpdates = 0;
		roundSeen = 0;
		updatesIntotal = 0;
		//update action probs
		highestScore = -Double.MAX_VALUE;
		routine = new HashMap<ArrayList<Double>, Double>();
		initActRoutine = new HashMap<>();
		
		//every time get to this point, meaning we have one more time of record of how many random restart have been tried
		if(currentRound < 5 && !ifFirstStep){
			_visCounter.randomTime ++;
			_visCounter.updateTime ++;
			_visCounter.SeenTime ++;
			_visCounter.depthTime ++;
			_visCounter.sizeTime ++;
		}
		t0 = System.currentTimeMillis();
		
		// declare a action list
		ArrayList<PVAR_INST_DEF> actions = new ArrayList<RDDL.PVAR_INST_DEF>();
		
		//recalculate the rootinit
		//because we assume there is no constrint so simple use concurrency divided by number of action bits
		if(countActBits == 0){
			for(PVAR_NAME p: s._alActionNames){
				countActBits += s.generateAtoms(p).size();
			}
		}
		
		//adjust maxVarDepth so that maxVarDepth * countActBits > baseVarNum
		// final F function
		INSTANCE instance = _rddl._tmInstanceNodes.get(_sInstanceName);
		if(searchDepth == -1){
			maxDepth = (instance._nHorizon - currentRound)  > instance._nHorizon ? instance._nHorizon : (instance._nHorizon - currentRound);
		}
		else{
			maxDepth = (instance._nHorizon - currentRound)  > searchDepth ? searchDepth : (instance._nHorizon - currentRound);
		}
		//counter = 0;
		stopAlgorithm = false;
		
		//initialize action prob
		ArrayList<Double> actionProb = null;

		//beacuase maxVarDpeth could be too small when
		if (searchDepth == -1) {
			maxVarDepth = expectMaxVarDepth;
		}
		else {
			maxVarDepth = searchDepth < expectMaxVarDepth ? searchDepth : expectMaxVarDepth;
		}
		
		//decide using dynamic depth
		//searchDepth = -1;
		//decide using conformant
		if(theRatio == -1 && maxVarDepth >= 1) {
			//use fixed conformant depth
			System.out.println("Use conformant depth: " + maxVarDepth);
		}
		else {
			//use searchdepth * theRatio as conformant depth
			if(theRatio != -1 && maxVarDepth == -1) {
				System.out.println("Use conformant depth as ratio: " + theRatio);
			}
			else {
				try {
					throw new Exception("theRatio or maxVarDepth set incorrectly. Please check conformant set up!");
				} catch (Exception e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
		
		//clear the state history
		//ready for building new history record
		stateHistory = new ArrayList<>();
		//initialize action variables in graph or not
				ifInGraph = new Boolean[countActBits * maxVarDepth];
				ifForcednotChoose = new Boolean[countActBits * maxVarDepth];
				for(int i = 0; i < countActBits * maxVarDepth; i ++) {
					ifInGraph[i] = false;
					ifForcednotChoose[i] = false;
				}
		
		TreeExp F = null;
		try {
			F = BuildF(s);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Long t1 = System.currentTimeMillis();

		
		//total number of updates used in this step

		actionProb = UpdateAllwtProj(s, F);
		
		//calculate the time and counts for this step
		double thisUpdateTime = System.currentTimeMillis() - t1;
		System.out.println(thisUpdateTime + " " + F.counter);
		double thisNumberNodesUpdates = F.counter * updatesIntotal;
		double thisTimePerNodeUpdate = thisUpdateTime / thisNumberNodesUpdates;
		//System.out.println("Average update time estimation based on single round: " + thisTimePerNodeUpdate);
		//System.out.println("This step bumber of nodes: " + (long)Math.ceil(thisNumberNodesUpdates));
		//System.out.println("avg dradient cost: " + gradientCost / thisNumberNodesUpdates);
		//System.out.println("avg fndalpa cost: " + fndalhpaCost / thisNumberNodesUpdates);
		timeHis.addLast(thisUpdateTime);
		nodesupdateHis.addLast(thisNumberNodesUpdates);
		if(thisNumberNodesUpdates > 0 && timeHis.size() > 3) {
			timeHis.removeFirst();
			nodesupdateHis.removeFirst();
		}
		timeUsedForCal = 0;
		numberNodesUpdates = 0;
		//for(int j = 0; j < timeHis.size(); j ++) {
		for(int j = timeHis.size() - 1; j >= 0; j --) {
			if(nodesupdateHis.get(j) > 0) {
				timeUsedForCal = timeHis.getLast();
				numberNodesUpdates = nodesupdateHis.getLast();
				break;
			}
		}
		//}
		
		
		
		
		//System.out.println("Routine records:");
		//System.out.println(bestNumAct);
		//System.out.println(highestScore);
		
		//state history is not useful any more
		//free the memory
		stateHistory.clear();
		stateHistory = null;
		
		//fnd conformant actions for each level
		ArrayList<ArrayList<PVAR_INST_DEF>> conformantActs = new ArrayList<>();
		SampleAction(s, conformantActs, bestNumAct);

		//ending work
		TreeExp.ClearHash();
		RDDL.ClearHash();
		
		if(ifPrintTraje) {
			System.out.println("********* trajectory actions **********");
			PrintTraje(conformantActs);
		}
		return conformantActs.get(0);
	}
	
	/*************************
	 * printing functions
	 *************************/
	public void PrintTraje(ArrayList<ArrayList<PVAR_INST_DEF>> conformantActs) {
		for(int h = 0; h < conformantActs.size(); h ++) {
			System.out.println("h = " + h + ": " + conformantActs.get(h));
		}
	}

	//call if want to print the trajectory actions from the new num actions
	public void PrintUpdateInRoutine(double val, State s, ArrayList<Double> closetAct) {
		
		System.out.println("\nUpdated the val to: " + val);
		ArrayList<ArrayList<PVAR_INST_DEF>> conformantActs = new ArrayList<>();
		try {
			SampleAction(s, conformantActs, closetAct);
		} catch (EvalException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		PrintTraje(conformantActs);
	}
	
	public ArrayList<PVAR_INST_DEF> EmergencyReturn(State s) throws Exception{
		System.out.println("Use EmergencyReturn of SOGBFOA!");
		
		ArrayList<Double> actionProb = new ArrayList<>();
		for(int i = 0; i < countActBits; i ++) {
			actionProb.add(0.0);
		}
		
		//needs to set conformant depth = 1
		//this will affect projection step
		//now we only think about the first step 
		// so it is fine to set it to be 1 here
		maxVarDepth = 1;
		stateHistory = null;
		stateHistory = new ArrayList<>();
		TEState theTS = new TEState().QuickCopy(s);
		stateHistory.add(theTS);
		for(int i = 0; i < actionProb.size(); i ++) {
			Policy.ifInGraph[i] = true;
			Policy.ifForcednotChoose[i] = false;
		}
		
		int actionCounter = 0;
		boolean ifAddIntTrans = int2PVAR.size() == 0;
		for(int h = 0; h < maxVarDepth; h ++) {
			trans2Tree.put(h, new HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, TreeExp>>());
			for (PVAR_NAME p : s._alActionNames) {
				trans2Tree.get(h).put(p, new HashMap<ArrayList<LCONST>, TreeExp>());
				ArrayList<ArrayList<LCONST>> terms = s.generateAtoms(p);
				//find list of types of the p_var_name
				PVARIABLE_DEF pvar_def = s._hmPVariables.get(p);
				//list of type names of the pvar
				ArrayList<TYPE_NAME> theTypeNames = pvar_def._alParamTypes;
				for (ArrayList<LCONST> t : terms) {
					trans2Tree.get(h).get(p).put(t, new TreeExp((Integer)actionCounter, null));
					//trans2Num.get(h).get(p).put(t, actionCounter);
					
					//add the var name and type names to associate with the number
					if(ifAddIntTrans) {
						int2PVAR.add(p);
						int2TYPE_NAME.add(theTypeNames);
						minimalProb.add(-Double.MAX_VALUE);
					}
					
					if(h == 0) {
						if(!act2Int.containsKey(p)) {
							act2Int.put(p, new HashMap<>());
						}
						act2Int.get(p).put(t, actionCounter);
					}
					actionCounter ++;
				}
			}
		}
		
		//initialize and copy states for trajcotry
		TEState as = new TEState();
		State cs = new State();
		cs = (State)DeepCloneUtil.deepClone(s);
		as.init(cs);
		
		//calculate concurrency
		if (ifConstructConstraints) {
			System.out.println("Rebuild constraints system!!!!");
			sumVars = new ArrayList<>();
			sumLimits = new ArrayList<>();
			sumLimitsExpr = new ArrayList<>();
			sumCoeffecients = new ArrayList<>();
			ifInSumConstraints = new Boolean[countActBits];
			Arrays.fill(ifInSumConstraints, false);
			try {
				as.AddExtraActionEff(trans2Tree.get(0), sumVars, sumLimits, sumLimitsExpr, sumCoeffecients);
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				System.exit(0);
			}
			GetRandomTrajAct(as);
			ifConstructConstraints = false;
		}
		
		//deal with hard constraints
		int countBase = 0;
		int pSize = 0;
		for(PVAR_NAME p: s._alActionNames) {
			ArrayList<ArrayList<LCONST>> ts = s.generateAtoms(p);
			if(Policy._extraEffects.containsKey(p)){
				//addVars.addAll(c)
				ArrayList<TYPE_NAME> typenames = s._hmPVariables.get(p)._alParamTypes;
				HashMap<ArrayList<TYPE_NAME>, ArrayList<BOOL_EXPR>> possibleMaches = Policy._extraEffects.get(p);
				Iterator it = possibleMaches.entrySet().iterator();
				//first figure out which are the variables used in for this PVAR_NAME
			    while (it.hasNext()) {
			    	Map.Entry pair = (Map.Entry)it.next();
			        //first decide if the type of each parameter is a subclass of the type of parameters in the preconditions
			        ArrayList<TYPE_NAME> constraintsTypeName = (ArrayList<RDDL.TYPE_NAME>)pair.getKey();
			        if(TEState.IfSuperClassList(typenames, constraintsTypeName)) {
			        	int countIndex = 0;
			        	for(ArrayList<LCONST> t: ts) {	
			        		//times each additional effects to the action variables
			        		for (BOOL_EXPR theAddEff : (ArrayList<BOOL_EXPR>)pair.getValue()) {
								RandomDataGenerator newR = new RandomDataGenerator();
								//laod the substituion of lvars into newsub
								//pass new sub to the sampling of the constraints
								HashMap<LVAR, LCONST> newSubs = new HashMap<>();
								//deal with each parameter appeared in the precondition
								for(int i = 0; i < Policy._extraEffectsLVARS.get(p).get(constraintsTypeName).size(); i ++) {
									//important:
									// we assume that there is no repetition of types in both the preconditions and action variable subs
									LVAR theVar = (LVAR)Policy._extraEffectsLVARS.get(p).get(constraintsTypeName).get(i);
									newSubs.put(theVar, t.get(i));
								}
								if(newSubs.size() == 1 && theAddEff instanceof PVAR_EXPR && ((PVAR_EXPR)theAddEff)._alTerms.size() == 1) {
									Map.Entry<LVAR, LCONST> entry = newSubs.entrySet().iterator().next();
									LVAR key = entry.getKey();
									if(!key.toString().equals(((PVAR_EXPR)theAddEff)._alTerms.get(0).toString())) {
										LCONST value = entry.getValue();
										newSubs.put((LVAR)((PVAR_EXPR)theAddEff)._alTerms.get(0), value);
									}
								}
								TreeExp theT = TEState.toTExp(theAddEff.sample(newSubs, theTS, newR), null);
								if(theT.Is0()) {
									Policy.ifForcednotChoose[countBase + countIndex] = true;
									break;
								}
							}
				        	countIndex ++;
			        	}
			        }
			    }
			    //System.out.println(Policy.ifForcednotChoose);
			}
			countBase += ts.size();
		}
		
		Projection(actionProb);
		ArrayList<ArrayList<PVAR_INST_DEF>> conformantActs = new ArrayList<>();
		ArrayList<Double> sampleAct = SampleNumAct(actionProb, s);
		SampleAction(s, conformantActs, sampleAct);
		System.out.println("Emergency return: " + conformantActs.get(0));
		return conformantActs.get(0);
	}
}
