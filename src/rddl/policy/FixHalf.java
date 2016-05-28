package rddl.policy;

import java.lang.reflect.Array;
import java.nio.channels.SeekableByteChannel;

import rddl.competition.Records;

import java.security.AllPermission;
import java.util.*;

import javax.naming.InitialContext;
import javax.xml.soap.SAAJMetaFactory;

import org.apache.xerces.impl.xpath.XPath.Step;

import rddl.TreeExp;
import rddl.TEState;
import rddl.EvalException;
import rddl.RDDL;
import rddl.RDDL.*;
import rddl.State;
import rddl.parser.parser;
import rddl.viz.GenericScreenDisplay;
import rddl.viz.NullScreenDisplay;
import rddl.viz.StateViz;
import rddl.RDDL.INSTANCE;
import rddl.RDDL.ENUM_TYPE_DEF;
import rddl.RDDL.LCONST;
import rddl.RDDL.LVAR;
import rddl.RDDL.PVARIABLE_DEF;
import rddl.RDDL.PVAR_INST_DEF;
import rddl.RDDL.PVAR_NAME;
import util.Permutation;

public class FixHalf extends Policy {
	
	public FixHalf () { 
		super();
	}
	
	public FixHalf(String instance_name) {
		super(instance_name);
	}
	boolean ifConverge = false;
	final double convergeNorm = 0.01;
	//if we only do certain nubber of pdates
	//we cannot see the overall trends of ratio action seen/updates
	//so we use this to adjust our estimate
	//so action seen at each step = actionSeen / staCounter * actionEstimateAdj
	final double actionEstimateAdj = 1;
	//const for random policy
	double randomAction = 1.0 / 2;
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
	int maxVarDepth = 0;
	long t0 = 0;
	//final int iterationTime = 10;
	int countActBits = 0;
	//if time out
	boolean stopAlgorithm = false;
	//int counter;
	//if use multi layer vars
	final boolean ifMultiLayer = false;
	final boolean ifAllVar = true;
	//min number of varibales
	int baseVarNum = 200;       
	
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
	
	int SearchDepth = -1;
	
	final boolean ifPrintProb = false;
	//print out the starting and ending points of each random restart
	final boolean ifPrintGrid = false;
	
	//specially for elevator
	boolean ifOldEle = false;
	boolean ifNewEle = false;
	
	final boolean ifDefaultNoop = true;
	
	// if we already go over this depth, we use calculation rather than real estimate
	final int MaxEstimateDepth = 10;
	
	//if use forward accumulation or reverse accumulation
	final boolean ifReverseAccu = true;
	
	final double fixAlpha = -1;
	
	final boolean ifRecordRoutine = true;
	
	final boolean ifTopoSort = true;
	
	/*
	int bit1Count = 0;
	int bit2Count = 0;
	int bit3Count = 0;
	int bit4Count = 0;
	int bitNoCount = 0;
	*/
	
	int maxDepth = 0;
	
	//stats
	double roundRandom = 0;
	double roundUpdates = 0;
	double roundSeen = 0;
	
	
	ArrayList<Double> bestNumAct = new ArrayList<Double>();
	double highestScore = -Double.MAX_VALUE;
	HashMap<ArrayList<Double>, Double> routine = new HashMap<ArrayList<Double>, Double>();
	//ArrayList<ArrayList<Double>> triedAct = new ArrayList<ArrayList<Double>>();
	
	//a table transfers from actions to numbers
	//HashMap<Integer, HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, Integer>>> trans2Num = new HashMap<Integer, HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Integer>>>();
	HashMap<Integer, HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, TreeExp>>> trans2Tree = new HashMap<Integer, HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,TreeExp>>>();
	//build the reward expectation function
	// with only the root level actions as variable
	// the other levels actions are treated as constant
	
	TreeExp BuildF(State s) throws EvalException{
		
		// final F function
		INSTANCE instance = rddl._tmInstanceNodes.get(_instanceName);
		//SearchDepth = -1;
		DOMAIN domain = rddl._tmDomainNodes.get(instance._sDomain);
		double cur_discount = 1;
		
		int actionCounter = 0;
		for (int h = 0; h < maxVarDepth; h++) {
			trans2Tree.put(h, new HashMap<PVAR_NAME, HashMap<ArrayList<LCONST>, TreeExp>>());
			for (PVAR_NAME p : s._alActionNames) {
				trans2Tree.get(h).put(p, new HashMap<ArrayList<LCONST>, TreeExp>());
				ArrayList<ArrayList<LCONST>> terms = s.generateAtoms(p);
				for (ArrayList<LCONST> t : terms) {
					
					trans2Tree.get(h).get(p).put(t, new TreeExp((Integer)actionCounter, null));
					//trans2Num.get(h).get(p).put(t, actionCounter);
					actionCounter ++;
				}
			}
		}
		
		
		// Q function
		TreeExp F = new TreeExp(0.0, null);

		// initialize
		TEState as = new TEState();
		State cs = new State();
		cs = (State)DeepCloneUtil.deepClone(s);
		as.init(cs);
		
		//this is the "actionProb" used to estimate average time consuming for one iteration
		//because it needs to be use d at each step, prepare it here
		

		//push forward until time estimate ilustrats that we cannot push more
		//int maxDepth;

		
		int h = 0;
		long oldTimeLeft = _timeAllowed;
		long oldUpdate = 0;
		long buildTreeTime = 0;
		//int buildTreeCounter = 0;
		long updateTimeDifference = 0;
		int staCounter = 0;
		long estimateBuildTree = 0;
		long estimateDifference = 0;
		long baseUpdateTime = 0;
		double seesActionEachStep = 0;
		double estimateUpdate = 0;
		double actionSeen = 0;
		routine.clear();
		for (; h < maxDepth; h++) {
			//actions
			ArrayList<PVAR_INST_DEF> trajeActs = new ArrayList<RDDL.PVAR_INST_DEF>();
			// check time
			if ((System.currentTimeMillis() - t0) > _timeAllowed ) {
				break;
			}
			if(h < maxVarDepth){
				for (PVAR_NAME p : as._alActionNames) {
					for (ArrayList<LCONST> t : as.generateAtoms(p)) {
						trajeActs.add(new PVAR_INST_DEF(p._sPVarName,
								(Object) trans2Tree.get(h).get(p).get(t), t));
					}
				}
			}
			else{
				for (PVAR_NAME p : as._alActionNames) {
					for (ArrayList<LCONST> t : as.generateAtoms(p)) {
						trajeActs.add(new PVAR_INST_DEF(p._sPVarName,
								(Object)new TreeExp((Double)randomAction, null), t));
					}
				}
			}
			
			
			
			as.SetActNoCompute(trajeActs);
			
			TreeExp reward = TEState.toTExp(domain._exprReward.sample(new HashMap<LVAR, LCONST>(), as, _random), null);
			
			F = (TreeExp)RDDL.ComputeArithmeticResult(F, RDDL.ComputeArithmeticResult(reward, cur_discount, "*"), "+");
			
			if(ifRecord){
				Records r = new Records();
				r.fileAppend("BUIlding2", "-state-\n");
				for (PVAR_NAME p : as._alStateNames) {
					for (ArrayList<LCONST> t : as.generateAtoms(p)) {
						r.fileAppend("BUIlding2", p._sPVarName + t.toString() + as.getPVariableAssign(p, t).toString() + "\n");
					}
				}
				
				r.fileAppend("BUIlding2", "-reward-\n");
				r.fileAppend("BUIlding2", reward.toString() + "\n");
				r.fileAppend("BUIlding2", "-F-\n");
				r.fileAppend("BUIlding2", F.toString() + "\n");
			}
			
			
			
			cur_discount *= instance._dDiscount;
			// output the current achieved depth
			if(ifPrint){
				System.out.println("finish: " + (h+1)+ " steps.");
			}
			
			//try three times of update
			if(SearchDepth == -1){
				if(ifReverseAccu){
				
					if(h <= MaxEstimateDepth){
						HashMap<TreeExp, Double> gradRec = new HashMap<TreeExp, Double>();
						HashMap<TreeExp, Double> valRec = new HashMap<TreeExp, Double>();
						//ArrayList<TreeExp> que = new ArrayList<TreeExp>();
						// long t000 = System.currentTimeMillis();
						//double estimateAvgIte = 0;
						//actionSeen = 0;
						long t00 = System.currentTimeMillis();
						
						
						
						staCounter ++;
						int a  = UpdateAllwtProjSimple(s, F);;
						if(!ifMultiLayer){
							actionSeen += a;
						}
						else{
							actionSeen = a;
						}
						/*
						int tryTimes = 10;
						for(int i = 1; i <= tryTimes; i ++){
							ArrayList<Double> varVal = new ArrayList<Double>();
							for(int j = 0; j < countActBits * maxVarDepth; j ++){
								varVal.add(_random.nextDouble());
						 	}
							
							
							ArrayList<TreeExp> queue = F.TopologQueue(ifTopoSort);
							ArrayList<Double> delta = new ArrayList<Double>();
							F.RevAccGradient(ifTopoSort, queue, delta, varVal);
							FndAlpha(s, F, varVal, delta);
							if (ifRecordRoutine) {
								UpdateRoutine(F, s, varVal, true);
							}

							actionSeen += routine.size();
							routine = new HashMap<ArrayList<Double>, Double>();
							
						}
						*/
						
						long t11 = System.currentTimeMillis();
						// if by estimate, the total time for doing numOfIte times
						// of updates is more than 90% of time left
						// stop, because this mean if we push forward more, we will
						// have no time to finish iterations
						long thisTImeUpdate = t11 - t00;
						baseUpdateTime = thisTImeUpdate;
						long timeLeft = (long) (_timeAllowed - (System.currentTimeMillis() - t0));
						if(h >= 1){
							long thisBuildTreeT = oldTimeLeft - timeLeft - thisTImeUpdate;
							//update time is an arithmatic sequence
							//thisDifference is the difference of the sequence
							long thisDifference = (thisTImeUpdate - oldUpdate);
							if(thisDifference < 0){
								thisDifference = 0;
							}
							buildTreeTime += thisBuildTreeT;
							updateTimeDifference += thisDifference;
							
							seesActionEachStep = actionSeen / (ifMultiLayer?1 : staCounter);
							
							//estimate t_treeBUIlding_h+1
							estimateBuildTree = buildTreeTime / staCounter;
							//estimate (t_update_h+1 - t_update_h)
							estimateDifference = updateTimeDifference / staCounter;
							//estimate t_update_h+1
							estimateUpdate = Double.valueOf(thisTImeUpdate + estimateDifference) / tryUpdates * numOfIte;
							//if we are under depth of MaxEstimate
							// only when timeLeft > t_update_h+1 + t_treeBuilding_h+1
							// do we continue building the tree to next level
							if(ifPrintEst){
								System.out.println("We estimate building Tree takes: " + estimateBuildTree + ", update takes: "
										+ estimateUpdate + " for " + numOfIte + " updates, while time allowed is: " + timeLeft);
							}
							if ( estimateUpdate + estimateBuildTree > timeLeft) {
								// for consistency
	
								h++; 
								
								break;
							}
						}
						oldTimeLeft = timeLeft;
						oldUpdate = thisTImeUpdate;
					}
					else{
						long timeLeft = (long) (_timeAllowed - (System.currentTimeMillis() - t0));
						estimateUpdate = Double.valueOf(baseUpdateTime + (h - MaxEstimateDepth) * estimateDifference) / seesActionEachStep * numOfIte;
						if ( estimateUpdate + estimateBuildTree > timeLeft) {
							// for consistency
							h++; 
							System.out.println("We estimate building Tree takes: " + estimateBuildTree + ", update takes: "
									+ estimateUpdate + " for " + numOfIte + " actions, while time allowed is: " + timeLeft);
							break;
						}
					}
				}
				else{
					ArrayList<Double> varVal = new ArrayList<Double>();
					for(int j = 0; j < countActBits * (maxVarDepth); j ++){
						varVal.add(_random.nextDouble());
					}
					HashMap<TreeExp, Double> gradRec = new HashMap<TreeExp, Double>();
					HashMap<TreeExp, Double> valRec = new HashMap<TreeExp, Double>();
					long t00 = System.currentTimeMillis();
					F.GetGradient(0, varVal, gradRec, valRec);
					F.GetGradient(1, varVal, gradRec, valRec);
					F.GetGradient(2, varVal, gradRec, valRec);
					long t11 = System.currentTimeMillis();
					//if by estimate, the total time for doing numOfIte times of updates is more than 90% of time left
					//stop, because this mean if we push forward more, we will have no time to finish iterations
					double estimateAvgIte = (t11 - t00) / 3;
					long timeLeft = (long)(_timeAllowed * 0.6) - (t11 - t0);
					int estLayer = h < maxVarDepth ? h : maxVarDepth;
					if( estimateAvgIte * countActBits * numOfIte > timeLeft * 0.9){
						System.out.println("Estimate time for each iteration: " + estimateAvgIte + ", and we will have " + numOfIte + ", while time allowed is: " + timeLeft);
						//for consistency
						h ++;
						break;
					}
				}
			}
			
			if(h!=maxDepth - 1){
				as.computeNextState(_random);
				as.advanceNextState();
			}
			
		}
		/*
		//cut the nodes that are not in F tree
		for(PVAR_NAME p: as._alStateNames){
			for(ArrayList<LCONST> t: as.generateAtoms(p)){
				TreeExp theVar = as._state.get(p).get(t);
				if(theVar.father.size() == 0){
					if(theVar.subExp != null){
					
						for (TreeExp child : theVar.subExp) {
							child.father.remove(theVar);
						}
					}
				}
			
			}
		}
		*/
		if(currentRound < 5)
		_visCounter.depthInTotal += h;
		System.out.println(h);
		
		System.out.println("finish: " + (h+1) + " steps.");
		
		if(maxVarDepth > h){
			maxVarDepth = h;
		}
		if(ifPrint)
		System.out.println("We are finally using " + maxVarDepth + "-layer variables");
		
		//int a = F.Size(new ArrayList<TExp>());
		//System.out.println(F);
		
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
				Projection(s._nMaxNondefActions, tempActProb);

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
	
	public void ProjectionByList(double sumLimit, ArrayList<Double> actionProb){
		
		
		//used to do hueristically projection
		double sumOfProb = 0;
		//max of all action prob
		//also used for hueristical projection
		double maxOfProb = Double.NEGATIVE_INFINITY;
		
		for(int j = 0; j < actionProb.size(); j ++){
		
			double newVal = actionProb.get(j);
			
			//update sum to do projection
			sumOfProb += newVal;
			if(newVal > maxOfProb){
				maxOfProb = newVal;
			}
			
		}
		//do projection
		
			double sumP = sumOfProb;

			double adjustPar = Double.NaN;
			if(sumP > sumLimit){
				
				
					adjustPar = sumP - sumLimit;
					double theRemain = adjustPar;
					int notZero = 0;
					for(int j = 0; j < actionProb.size(); j ++){
						double theVal = actionProb.get(j);
						if(theVal > 0){
							notZero ++;
						}
					}
					while(theRemain > 0){
						double del = theRemain / notZero;
						theRemain = 0;
						notZero = 0;
						for(int j = 0; j < actionProb.size(); j ++){
							double oldVal = actionProb.get(j);
							if(oldVal == 0){
								continue;
							}
							double newVal = oldVal - del;
							actionProb.set(j, newVal < 0 ? 0 : newVal);
							if(newVal < 0){
								theRemain -= newVal;
							}
							if(newVal > 0){
								notZero ++;
							}
						}
					}
				
			
				
			
		}
	}
	
	public void Projection(int concurrency, ArrayList<Double> actionProb){
		
		
		ArrayList<Integer> morethan1Counter = new ArrayList<Integer>();
		for(int j = 0; j < maxVarDepth; j ++){
			morethan1Counter.add(0);
		}
		//used to do hueristically projection
		ArrayList<Double> sumOfProb = new ArrayList<Double>();
		for(int j = 0; j < maxVarDepth; j ++){
			sumOfProb.add(0.0);
		}
		//max of all action prob
		//also used for hueristical projection
		ArrayList<Double> maxOfProb = new ArrayList<Double>();
		for(int j = 0; j < maxVarDepth; j ++){
			maxOfProb.add(Double.NEGATIVE_INFINITY);
		}
		for(int j = 0; j < actionProb.size(); j ++){
			int currentDepth = j / countActBits;
			double newVal = actionProb.get(j);
			if(newVal > 1){
				morethan1Counter.set(currentDepth, morethan1Counter.get(currentDepth)+1);
			}
			//update sum to do projection

			sumOfProb.set(currentDepth, sumOfProb.get(currentDepth) + newVal);
			if(newVal > maxOfProb.get(currentDepth)){
				maxOfProb.set(currentDepth, newVal);
			}
			
		}
		//do projection
		for(int h = 0; h < maxVarDepth; h ++){
			
			//************This is for elevator use*************//
			if(ifOldEle || ifNewEle){
				int numOfAct = 0;
				if(ifOldEle){
					numOfAct = 3;
				}
				if(ifNewEle){
					numOfAct = 4;
				}
				for(int i = 0; i < concurrency; i ++){
					ArrayList<Double> eleList = new ArrayList<Double>();
					for(int j = 0; j < numOfAct; j ++){
						eleList.add(actionProb.get(h * countActBits + i+j*concurrency));
						
					}
					ProjectionByList(1, eleList);
					for(int j = 0; j < numOfAct; j ++){
						
						actionProb.set(h * countActBits + i+j*concurrency, eleList.get(j));
						
					}
				}
				
				//max of all action prob
				//also used for hueristical projection
				
				maxOfProb.set(h, Double.NEGATIVE_INFINITY);
				morethan1Counter.set(h, 0);
				sumOfProb.set(h, 0.0);
				for(int j = h*countActBits; j < (h+1)*countActBits; j ++){
					double newVal = actionProb.get(j);
					if(newVal > 1){
						morethan1Counter.set(h, morethan1Counter.get(h)+1);
					}
					//update sum to do projection

					sumOfProb.set(h, sumOfProb.get(h) + newVal);
					if(newVal > maxOfProb.get(h)){
						maxOfProb.set(h, newVal);
					}
					
				}
			}
			
			//*********ele use end here********************//
			
			double sumP = sumOfProb.get(h);

			double adjustPar = Double.NaN;
			if(sumP > concurrency){
				if(ifProjectwtTime){
					adjustPar = concurrency / sumP;
					for(int j = 0; j < countActBits; j ++){
						actionProb.set(h * countActBits + j, actionProb.get(h * countActBits + j) * adjustPar);
					}
				}
				else{
					adjustPar = sumP - concurrency;
					double theRemain = adjustPar;
					int notZero = 0;
					for(int j = 0; j < countActBits; j ++){
						double theVal = actionProb.get(h * countActBits + j);
						if(theVal > 0){
							notZero ++;
						}
					}
					while(theRemain > 0){
						double del = theRemain / notZero;
						theRemain = 0;
						notZero = 0;
						for(int j = 0; j < countActBits; j ++){
							double oldVal = actionProb.get(h * countActBits + j);
							if(oldVal == 0){
								continue;
							}
							double newVal = oldVal - del;
							actionProb.set(h * countActBits + j, newVal < 0 ? 0 : newVal);
							if(newVal < 0){
								theRemain -= newVal;
							}
							if(newVal > 0){
								notZero ++;
							}
						}
					}
				}
			}
		
				
			
		}
		
		
		
		
		
	}
	


	public ArrayList<Double> UpdateAllwtProj(State s, TreeExp F) throws EvalException{

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
		RandomConcurrentPolicyIndex actionGen = new RandomConcurrentPolicyIndex(s);
		//only used for revAcc
		ArrayList<TreeExp> que = new ArrayList<TreeExp>();
		
		//long t000 = System.currentTimeMillis();
		if(ifReverseAccu){
			que = F.TopologQueue(ifTopoSort);
		}
		
		
		boolean ifFirstTime = true;
		while(!stopAlgorithm){
			double updatedasCounter = 0;
			//a record of how many times we keep decreasing Q
			//sometims because alpha is too large the Q keeps going down
			//if that happens for enough many times we simply force it to cenverge
			
			
			
			
			//get concrete actions
			//ifPrintInitial = true;
			
			if(!ifMultiLayer){
				if(actionGen.already.size() < actionGen.possibleComb){
					
					ArrayList<Integer> conAct = actionGen.getNAction(s);
					
					
					if(!conAct.contains(-1)){
						
						for (int i = 0; i < countActBits; i++) {
							actionProb.set(i, 0.0);
						}
						for(int i = countActBits; i < actionProb.size(); i ++){
							actionProb.set(i, _random.nextDouble());
						}
						for(Integer con: conAct){
									
							actionProb.set(con, 1.0);
									
						}
						Projection(s._nMaxNondefActions, actionProb);
					}
					else{
						for (int i = 0; i < actionProb.size(); i++) {
							actionProb.set(i, _random.nextDouble());
						}
						Projection(s._nMaxNondefActions, actionProb);
						ifPrintInitial = false;
					}
					
				}
				else{
					for (int i = 0; i < actionProb.size(); i++) {
						actionProb.set(i, _random.nextDouble());
					}
					Projection(s._nMaxNondefActions, actionProb);
					ifPrintInitial = false;
				}
			}
			else{
				ArrayList<Integer> conAct = null;
				if(actionGen.already.size() < actionGen.possibleComb){
					
					conAct = actionGen.getNAction(s);

					if (!conAct.contains(-1)) {

						for (int i = 0; i < countActBits; i++) {
							actionProb.set(i, 0.0);
						}
						
						for (Integer con : conAct) {

							actionProb.set(con, 1.0);

						}
						//Projection(s._nMaxNondefActions, actionProb);
					} else {
						for (int i = 0; i < countActBits; i++) {
							actionProb.set(i, _random.nextDouble());
						}
						Projection(s._nMaxNondefActions, actionProb);
						
					}
					if(ifFirstTime){
						for (int i = countActBits; i < actionProb.size(); i++) {
							actionProb.set(i, _random.nextDouble());
						}
						Projection(s._nMaxNondefActions, actionProb);
						ifFirstTime = false;
					}
				}
				else{
					for (int i = 0; i < countActBits; i++) {
						actionProb.set(i, _random.nextDouble());
					}
					Projection(s._nMaxNondefActions, actionProb);
				}
				
				
				if(ifPrintInitial){
					System.out.println("Starting the restarts at: " + conAct);
				}
			}
			
			
			
			
			/*
			for(int i = 0; i < actionProb.size(); i ++){
				actionProb.set(i, 0.5);
			}
			*/
				
				
			
			if(ifPrintGrid){
				ArrayList<Integer> alreadyIn = new ArrayList<Integer>();
				for(int i = 1; i <= s._nMaxNondefActions; i ++){
					double maxVal = -1;
					int maxJ = -1;
					for(int j = 0; j < actionProb.size(); j ++){
						double val = actionProb.get(j);
						if(alreadyIn.contains(j)){
							continue;
						}
						if(val > maxVal){
							maxVal = val;
							maxJ = j;
						}
					}
					if(maxVal < randomAction){
						break;
					}
					alreadyIn.add(maxJ);
				}
				System.out.print("\n\nSta: ");
				for(int j: alreadyIn){
					System.out.print(j + " ");
				}
			}
			//iteratively update action probs until converge
			ifConverge = false;
			//a value table to record the realvalue of trees
			//only used in one iteration
			//need to be clear after use
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
			
			//ba sed on this Q value, setup threshold
			if(oldQ != 0){
				ConvergeT = Math.abs(oldQ * RelativeErr);
			}
			else{
				ConvergeT = RelativeErr;
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
			for(int a = 0; a < maxVarDepth * countActBits; a ++){
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
			
			
			
			
			while(!ifConverge && !stopAlgorithm){

				//calculate delta
				ArrayList<Double> delta = new ArrayList<Double>();
				//System.out.println("");
				//this step gets delta for each bit
				if(ifReverseAccu){
					//ArrayList<TreeExp> visited = new ArrayList<TreeExp>();
					//int queSize = F.Size(visited);
					F.RevAccGradient(ifTopoSort, que, delta, actionProb);
					
					//System.out.println(que.get(0));
					//System.out.println(gTree.toString());
					if(ifPrintBit){
						for(int i = 0; i < actionProb.size(); i ++){
							System.out.println("d for " + "v" + i + " " + delta.get(i));
						}
					}
					for(int i = 0; i < delta.size(); i ++){
						double d = delta.get(i);
						if(d != 0){
							ifthisBitChange.set(i, true);
						}
					}
					//System.out.println(System.currentTimeMillis() - t000);
					
				}
				else{
					
					for(int i = 0; i < actionProb.size(); i ++){
						
						double d = F.GetGradient(i, actionProb, gradRec, valRec);
						
						if(ifPrintBit){
							System.out.println("d for " + "v" + i + " " + d);
						}
						
						if(i < countActBits && d != 0){
							ifthisBitChange.set(i, true);
						}
						gradRec.clear();
						delta.add(d);
					}
					//System.out.println(System.currentTimeMillis() - t000);
				}
				
				updatedasCounter ++;
				//this step updates prob and return the Q
				newQ = FndAlpha(s, F, actionProb, delta);
				//System.out.println(routine.size());
				if(ifRecordRoutine){
					UpdateRoutine(F, s, actionProb, true);
				}
				//System.out.println(routine.size());
				/*
				if(currentRound == 1){
				for(int i = 0; i < actionProb.size(); i ++){
					actionProb.set(i, 0.0);
				}
				actionProb.set(3, 1.0);
				}
				*/
				if(ifPrintBit){
					for(int a = 0; a < actionProb.size(); a++){
						System.out.println("a for " + "v" + a + " " + actionProb.get(a));
					}
					//System.out.println();
				}
				
				
				
				//now alphas are changed so we need to clear the value record in the tree
				valRec.clear();
				
				
				if(ifPrint){
					System.out.println("oldQ: " + oldQ + "\n");
					System.out.println("newQ: " + newQ + "\n");
				}
				
				
				if(convergeNorm == -1 && Math.abs(newQ - oldQ) < ConvergeT){
					ifConverge = true;
				}
				
				oldQ = newQ;
				//we don't need to clear valrec again
				//because the value when calculating newQ can be reused in next iteration
				if(System.currentTimeMillis() - t0 > _timeAllowed){
					stopAlgorithm = true;
					break;
				}
			}
			if(ifPrintGrid){
				ArrayList<Integer> alreadyIn = new ArrayList<Integer>();
				for(int i = 1; i <= s._nMaxNondefActions; i ++){
					double maxVal = -1;
					int maxJ = -1;
					for(int j = 0; j < actionProb.size(); j ++){
						double val = actionProb.get(j);
						if(alreadyIn.contains(j)){
							continue;
						}
						if(val > maxVal){
							maxVal = val;
							maxJ = j;
						}
					}
					if(maxVal < randomAction){
						break;
					}
					alreadyIn.add(maxJ);
				}
				System.out.print("\nEnd: ");
				for(int j: alreadyIn){
					System.out.print(j + " ");
				}
				
			}
			//converged; continue to next random restart
			
			if(newQ != initialQ){
				roundRandom ++;
				roundUpdates += updatedasCounter;
				if(currentRound < 5){
					_visCounter.updatesInTotal += updatedasCounter;
					_visCounter.randomInTotal ++;
				}
				
				
				//randomRestart ++;
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
				//if dead bit set to 0
				 
				if(ifDefaultNoop){
					for (int a = 0; a < countActBits; a++) {
						if (!ifthisBitChange.get(a)) {
							bestActionProb.set(a, 0.0);
						}
					}
				}
				
				/*
				System.out.println("Q is updated to: " + newQ); 
				
				System.out.println("Best action prob is updated to: ");
				for(int a = 0; a < countActBits; a ++){
					System.out.println(actionProb.get(a));
				}
				*/
				
			}
			else{
				if(ifPrint){
					System.out.println("Failed to update Q. Previous best is: " + bestQ + " and now the Q is: " + newQ); 
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

		//System.out.println(completeBest);
		
		return bestActionProb; 
	}
	
	//this function is used to estimate update cost
	// it works exactly like the complete function but doesn't change statistics or any globle var
	public int UpdateAllwtProjSimple(State s, TreeExp F) throws EvalException{

		ArrayList<Double> actionProb = new ArrayList<Double>();
		for(int i = 0; i < countActBits * maxVarDepth; i ++){
			actionProb.add(0.0);
		} 
		
		//ArrayList<TExp> visited = new ArrayList<TExp>();
		//int b = F.Size(visited );
		//iteration counter
		int randomRestart = 0;
		
		//Record the best actionProb that gets the highest Q value in F tree
		ArrayList<Double> bestActionProb = new ArrayList<Double>();
		for(int i = 0; i < countActBits; i ++){
			bestActionProb.add(0.0);
		}
		double bestQ = Double.NEGATIVE_INFINITY;

		//generate concrete actions for getting the starting point of rrs
		RandomConcurrentPolicyIndex actionGen = new RandomConcurrentPolicyIndex(s);
		//only used for revAcc
		ArrayList<TreeExp> que = new ArrayList<TreeExp>();
		
		//long t000 = System.currentTimeMillis();
		if(ifReverseAccu){
			que = F.TopologQueue(ifTopoSort);
		}
		
		int updatedasCounter = 0;
		while(!stopAlgorithm){
			
			randomRestart ++;
			//get concrete actions
			//ifPrintInitial = true;
			if(actionGen.already.size() < actionGen.possibleComb){
				
				ArrayList<Integer> conAct = actionGen.getNAction(s);
				
				
				if(!conAct.contains(-1)){
					
					for (int i = 0; i < countActBits; i++) {
						actionProb.set(i, 0.0);
					}
					for(int i = countActBits; i < actionProb.size(); i ++){
						actionProb.set(i, _random.nextDouble());
					}
					for(Integer con: conAct){
								
						actionProb.set(con, 1.0);
								
					}
					
				}
				else{
					for (int i = 0; i < actionProb.size(); i++) {
						actionProb.set(i, _random.nextDouble());
					}
					Projection(s._nMaxNondefActions, actionProb);
					ifPrintInitial = false;
				}
				
			}
			else{
				for (int i = 0; i < actionProb.size(); i++) {
					actionProb.set(i, _random.nextDouble());
				}
				Projection(s._nMaxNondefActions, actionProb);
				ifPrintInitial = false;
			}
			
			/*
			for(int i = 0; i < actionProb.size(); i ++){
				actionProb.set(i, 0.5);
			}
			*/

			//iteratively update action probs until converge
			ifConverge = false;
			//a value table to record the realvalue of trees
			//only used in one iteration
			//need to be clear after use
			HashMap<TreeExp, Double> valRec = new HashMap<TreeExp, Double>();
			HashMap<TreeExp, Double> gradRec = new HashMap<TreeExp, Double>();
			//initialize oldQ to be realvalue calculated with initial action prob
			double oldQ = F.RealValue(actionProb, valRec);
			if(ifRecordRoutine){
				UpdateRoutine(F, s, actionProb, false);
			}
			//this is used to judge whether Q has been changed
			double initialQ = oldQ;

			
			//ba sed on this Q value, setup threshold
			if(oldQ != 0){
				ConvergeT = Math.abs(oldQ * RelativeErr);
			}
			else{
				ConvergeT = RelativeErr;
			}
			//update bestQ and action
			if(oldQ > bestQ){
				bestQ = oldQ;
				for(int a = 0; a < countActBits; a ++){
					bestActionProb.set(a, actionProb.get(a));
				}
			}
			
			//dead bit record
			//if during this random restart, certain bits never change, it means that Q is not related to it
			//set it to be 0
			//only for top level 
			ArrayList<Boolean> ifthisBitChange = new ArrayList<Boolean>();
			for(int a = 0; a < maxVarDepth * countActBits; a ++){
				ifthisBitChange.add(false);
			}

			//initialize newQ
			double newQ = 0; // this will be recalculated later

			while(!ifConverge && !stopAlgorithm){
				//calculate delta
				ArrayList<Double> delta = new ArrayList<Double>();
				//System.out.println("");
				//this step gets delta for each bit
				if(ifReverseAccu){
					//ArrayList<TreeExp> visited = new ArrayList<TreeExp>();
					//int queSize = F.Size(visited);
					F.RevAccGradient(ifTopoSort, que, delta, actionProb);
					

					for(int i = 0; i < delta.size(); i ++){
						double d = delta.get(i);
						if(d != 0){
							ifthisBitChange.set(i, true);
						}
					}
					//System.out.println(System.currentTimeMillis() - t000);
					
				}
				else{
					
					for(int i = 0; i < actionProb.size(); i ++){
						
						double d = F.GetGradient(i, actionProb, gradRec, valRec);

						if(i < countActBits && d != 0){
							ifthisBitChange.set(i, true);
						}
						gradRec.clear();
						delta.add(d);
					}
					//System.out.println(System.currentTimeMillis() - t000);
				}
				
				updatedasCounter ++;
				//this step updates prob and return the Q
				newQ = FndAlpha(s, F, actionProb, delta);
				//System.out.println(routine.size());
				if(ifRecordRoutine){
					UpdateRoutine(F, s, actionProb, false);
				}
				//System.out.println(randomRestart + " " + updatedasCounter + " " + routine.size());
				//now alphas are changed so we need to clear the value record in the tree
				valRec.clear();

				if(convergeNorm == -1 && Math.abs(newQ - oldQ) < ConvergeT){
					ifConverge = true;
				}
				
				oldQ = newQ;
				//we don't need to clear valrec again
				//because the value when calculating newQ can be reused in next iteration
				if(System.currentTimeMillis() - t0 > _timeAllowed){
					stopAlgorithm = true;
					break;
				}
				if(!ifMultiLayer){
					if(routine.size() >= trySeeing){
						
						if(ifPrint){
							System.out.println(trySeeing + "required, met!");
						}
						stopAlgorithm = true;
						break;
					}
				}
				else{
					if(updatedasCounter >= tryUpdates){
						stopAlgorithm = true;
						break;
					}
				}

			}


			//Get the Q value for this convergence
			if(newQ > bestQ){

				bestQ = newQ;
				for(int a = 0; a < countActBits; a ++){
					bestActionProb.set(a, actionProb.get(a));
				}
				//if dead bit set to 0
				 
				if(ifDefaultNoop){
					for (int a = 0; a < countActBits; a++) {
						if (!ifthisBitChange.get(a)) {
							bestActionProb.set(a, 0.0);
						}
					}
				}
			}	
		}
		int res = routine.size();
		routine.clear();
		stopAlgorithm = false;
		ifConverge = false;
		return res;
	}
	
	public ArrayList<Double> SampleNumAct(ArrayList<Double> varVal, State s){
		int size = varVal.size();
		boolean[] mute = new boolean[countActBits];
		double[] res = new double[countActBits]; 
		//only uses concrete action at top level
		//on all the other levels use fractional action
		
		
		for(int h = 0; h < 1; h ++){
			for(int i = 1; i <= s._nMaxNondefActions; i ++){
				double max = -Double.MAX_VALUE;
				int maxIndex = -1;
				for(int j = h * countActBits; j < (h+1) * countActBits; j ++){
					if(!mute[j] && varVal.get(j) > max){
						max = varVal.get(j);
						maxIndex = j;
					}
				}
				if(max > randomAction){
					res[maxIndex] = 1;
					mute[maxIndex] = true;
					if(ifOldEle){
						int numfEle = countActBits / 3;
						int remain = maxIndex % numfEle;
						for(int k = 0; k < 3; k ++){
							mute[remain + k * numfEle + h * countActBits] = true;
						}
					}
					if(ifNewEle){
						int numfEle = countActBits / 4;
						int remain = maxIndex % numfEle;
						for(int k = 0; k < 4; k ++){
							mute[remain + k * numfEle + h * countActBits] = true;
						}
					}
				}
				else{
					break;
				}
			}
		}
		/*
		Random rand = new Random();
		for(int h = 0; h < 1; h ++){
			int countTure = 0;
			for (int j = h * countActBits; j < (h + 1) * countActBits; j++) {
				if (!mute[j] && rand.nextDouble() <= varVal.get(j)) {
					res[j] = 1;
					countTure++;
					if (ifOldEle) {
						int numfEle = countActBits / 3;
						int remain = j % numfEle;
						for (int k = 0; k < 3; k++) {
							mute[remain + k * numfEle + h * countActBits] = true;
						}
					}
					if (ifNewEle) {
						int numfEle = countActBits / 4;
						int remain = j % numfEle;
						for (int k = 0; k < 4; k++) {
							mute[remain + k * numfEle + h * countActBits] = true;
						}
					}
					if (countTure == s._nMaxNondefActions) {
						break;
					}
				}
			}
		}
		*/
		ArrayList<Double> numAct = new ArrayList<Double>();
		for(double r: res){
			numAct.add(r);
		}
		for(int j = countActBits; j < size; j ++){
			numAct.add(varVal.get(j));
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
		/*
		if(realAct.get(0) == 1){
			bit1Count ++;
		}
		else{
			if(realAct.get(1) == 1){
				bit2Count ++;
			}
			else{
				if(realAct.get(2) == 1){
					bit3Count ++;
				}
				else{
					
					if(realAct.get(3) == 1){
						bit4Count ++;
					}
					else{
					
						bitNoCount ++;
					}
				}
			}
		}
		*/
		//System.out.println(varVal);
		//System.out.println(realAct);
		//System.out.println();
		/*
		if(!triedAct.contains(realAct)){
			triedAct.add(realAct);
			_visCounter.SeenInTotal ++;
		}
		*/
		double val = 0;
		if(closestAct.size() > realAct.size()){
			HashMap<TreeExp, Double> valRec = new HashMap<TreeExp, Double>();
			val = F.RealValue(closestAct, valRec);
		}
		
		if(!routine.containsKey(realAct)){
			if(closestAct.size() == realAct.size()){
				HashMap<TreeExp, Double> valRec = new HashMap<TreeExp, Double>();
				val = F.RealValue(closestAct, valRec);
			}
			routine.put(realAct, val);
			if(ifStatistics){
				roundSeen ++;
				if(currentRound < 5){
					_visCounter.SeenInTotal ++;
				}
				
				
				if(val > highestScore){
					highestScore = val;
					bestNumAct = realAct;
				}
			}
			
		}
		else{
			if(closestAct.size() > realAct.size() && val > routine.get(realAct)){
				routine.put(realAct, val);
				if(ifStatistics && val > highestScore){
					highestScore = val;
					bestNumAct = realAct;
				}
			}
		}
		

	}
	
	//sample action from largest to smallest; build actions incrementally
	public ArrayList<PVAR_INST_DEF> SampleAction(State s) throws EvalException{
		ArrayList<PVAR_INST_DEF> finalAction = new ArrayList<RDDL.PVAR_INST_DEF>();
		int counter = 0;
		for(PVAR_NAME p: s._alActionNames){
			for(ArrayList<LCONST> t: s.generateAtoms(p)){
				if(bestNumAct.get(counter) == 1){
					finalAction.add(new PVAR_INST_DEF(p._sPVarName, (Object)true, t));
				}
				counter ++;
			}
		}
		return finalAction;
	}
	
	

	//sample action for each bit; until get a legal action or time out (returns noop at that case)
	//last parameter: if always add the bit with largest prob to action list so long as it's legal
	public ArrayList<PVAR_INST_DEF> SampleAction(ArrayList<Double> valProb, State conS, boolean ifKeeplargest, boolean ifHueristicChoice) throws EvalException{
		HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>> actionProb = new HashMap<PVAR_NAME,HashMap<ArrayList<LCONST>,Double>>();
		int counter = 0;
		for(PVAR_NAME p: conS._alActionNames){
			actionProb.put(p, new HashMap<ArrayList<LCONST>,Double>());
			for(ArrayList<LCONST> t: conS.generateAtoms(p)){

				actionProb.get(p).put(t, valProb.get(counter));
				counter ++;
			}
		}
		
		if(ifPrintProb){
			for(PVAR_NAME p: conS._alActionNames){
				for(ArrayList<LCONST> t: conS.generateAtoms(p)){
					System.out.println(p._sPVarName+t.toString()+actionProb.get(p).get(t));
				}
			}
		}
		
		//timer
		long t0 = System.currentTimeMillis();
		
		ArrayList<PVAR_INST_DEF> finalAction = new ArrayList<RDDL.PVAR_INST_DEF>();
		
		//if we hueristically choose actions
		//then first sample the number of final actions
		
		int numOfActions = -1;
		if(ifHueristicChoice){
			
			//numOfActions = r.nextInt(conS._nMaxNondefActions + 1);
			numOfActions = conS._nMaxNondefActions;
			for(int k = 1; k <= numOfActions; k ++){
				double maxProb = -1;
				PVAR_NAME bestName = null;
				ArrayList<LCONST> bestTerm = null;
		    	for (PVAR_NAME p : conS._alActionNames) {
					ArrayList<ArrayList<LCONST>> terms = conS.generateAtoms(p);
					for (ArrayList<LCONST> t : terms) {
						if (actionProb.get(p).get(t) > maxProb) {
							maxProb = actionProb.get(p).get(t);
							bestName = p;
							bestTerm = t;
						}
					}
				}
				if(maxProb >= randomAction){
					finalAction.add(new PVAR_INST_DEF(bestName._sPVarName, true, bestTerm));
					boolean passed_constraints = true;
					try{
						conS.checkStateActionConstraints(finalAction);
					}catch (EvalException e) { 
						// Got an eval exception, constraint violated
						passed_constraints = false;
							//System.out.println(actions + " : " + e);
							//System.out.println(s);
							//System.exit(1);
					} catch (Exception e) { 
						throw new EvalException(e.toString());
					}
					if(!passed_constraints){
						finalAction.remove(finalAction.size()-1);
					}
					//if succesfully keep the largest, set up its prob to be -10
					else{
						actionProb.get(bestName).put(bestTerm, -10.0);
					}
					if(finalAction.size() == conS._nMaxNondefActions){
						return finalAction;
					}
				}
				else{
					break;
				}
		    }
		}
		else{
			//deal with ifKeepLargest
			if (ifKeeplargest) {
				double maxProb = -1;
				PVAR_NAME bestName = null;
				ArrayList<LCONST> bestTerm = null;
				// find the largest prob
				for (PVAR_NAME p : conS._alActionNames) {
					ArrayList<ArrayList<LCONST>> terms = conS.generateAtoms(p);
					for (ArrayList<LCONST> t : terms) {
						if (actionProb.get(p).get(t) > maxProb) {
							maxProb = actionProb.get(p).get(t);
							 bestName = p;
							bestTerm = t;
						}
					}
				}
				if (maxProb >= randomAction) {
					finalAction.add(new PVAR_INST_DEF(bestName._sPVarName,
							true, bestTerm));
					boolean passed_constraints = true;
					try {
						conS.checkStateActionConstraints(finalAction);
					} catch (EvalException e) {
						// Got an eval exception, constraint violated
						passed_constraints = false;
						// System.out.println(actions + " : " + e);
						// System.out.println(s);
						// System.exit(1);
					} catch (Exception e) {
						throw new EvalException(e.toString());
					}
					if (!passed_constraints) {
						finalAction.remove(finalAction.size() - 1);
					}
					// if succesfully keep the largest, set up its prob to be
					// -10
					if (finalAction.size() == 1) {
						actionProb.get(bestName).put(bestTerm, -10.0);
					}
					if (finalAction.size() == conS._nMaxNondefActions) {
						return finalAction;
					}
				}
			}
			
			while(System.currentTimeMillis() - t0 < _timeAllowed * SampleTime){
				//sample each action bit, put them into the final action list
				//finally check if it's legal or not
				for(PVAR_NAME p: conS._alActionNames){
					for(ArrayList<LCONST> t: conS.generateAtoms(p)){
						double dice = _random.nextDouble();
						if(dice < actionProb.get(p).get(t)){
							finalAction.add(new PVAR_INST_DEF(p._sPVarName, true, t));

							//sample actions based on action prob until getting a legal action
							boolean passed_constraints = true;
							try{
								conS.checkStateActionConstraints(finalAction);
							} catch (EvalException e) {
								// Got an eval exception, constraint violated
								passed_constraints = false;
								// System.out.println(actions + " : " + e);
								// System.out.println(s);
								// System.exit(1);
							} catch (Exception e) {
								throw new EvalException(e.toString());
							}
							if (!passed_constraints) {
								finalAction.remove(finalAction.size()-1);
							}
							if(finalAction.size() == conS._nMaxNondefActions){
								return finalAction;
							}
						}
					}
				}
			}
		}
		return finalAction;
	}
	
	//final get action algorithm
	@Override
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
		//System.out.println(s);
		
		//initialization
		ifConverge = false;
		INSTANCE instance = rddl._tmInstanceNodes.get(_instanceName);
		SearchDepth = instance._nHorizon / 2;
		//const for random policy
		randomAction = 1.0 / 2;
		//double alpha = 0.00001;
		//convergence threashold
		//this is just init value. it will be adjusted by another par
		ConvergeT = 0.0000001;
		
		
		//how many times do we wanna update each action bit
		///numOfIte = 200;
		//if trySeeing  > ratioOftrials * # possbile act, then set numOfIte = ratioOftrials * # possbile act
		// meaning that by estimation, we only wanna see a certain ratio of all actions
		//otherwise it is wasting time
		//how many updates to make to do the estimate
		
		//ratioOfTrials = 0.3;

		//try seeing certain number of actions
		//trySeeing = 5;
		//the depth of variables that we reach
		//this is dynamic
		maxVarDepth = 0;
		//t0 = 0;
		//final int iterationTime = 10;
		//countActBits = 0;
		//if time out
		stopAlgorithm = false;

		//min number of varibales
		//baseVarNum = 200;       
		
		//base number of dived the alpha legal region
		//AlphaTime = 10;

		//ifPrintInitial = false;
		
		//SearchDepth = -1;

		
		//specially for elevator
		ifOldEle = false;
		ifNewEle = false;

		
		/*
		int bit1Count = 0;
		int bit2Count = 0;
		int bit3Count = 0;
		int bit4Count = 0;
		int bitNoCount = 0;
		*/
		
		//maxDepth = 0;
		
		//stats
		roundRandom = 0;
		roundUpdates = 0;
		roundSeen = 0;
		
		//update action probs
				highestScore = -Double.MAX_VALUE;
				routine = new HashMap<ArrayList<Double>, Double>();
		
		
		//every time get to this point, meaning we have one more time of record of how many random restart have been tried
		if(currentRound < 5){
			_visCounter.randomTime ++;
			_visCounter.updateTime ++;
			_visCounter.SeenTime ++;
			_visCounter.depthTime ++;
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
		
		if(SearchDepth == -1){
			maxDepth = (instance._nHorizon - currentRound)  > instance._nHorizon ? instance._nHorizon : (instance._nHorizon - currentRound);
		}
		else{
			maxDepth = (instance._nHorizon - currentRound)  > SearchDepth ? SearchDepth : (instance._nHorizon - currentRound);
		}
		if(ifAllVar){
			baseVarNum = countActBits * maxDepth;
		}
		maxVarDepth = 0;
		if(ifMultiLayer){
			
			maxVarDepth = -1;
			while(true){
				maxVarDepth ++;
				if(maxVarDepth == maxDepth || (maxVarDepth + 1) * countActBits >= baseVarNum){
					break;
				}
			}
		}
		maxVarDepth ++;
		
		//counter = 0;
		stopAlgorithm = false;
		
		//the real number of each action bit for taking random policy
		ArrayList<Double> comb = new ArrayList<Double>();
		Double numInTotal = 0.0;

		//caculate the number of choose k from n
		for(int k = 0; k <= s._nMaxNondefActions; k ++){
			int max = countActBits;
			double resu = 1;
			for(int j = 1; j <= k; j ++){
				resu *= max;
				max --;
			}
			for(int j = 2; j <= k; j ++){
				resu /= j;
			}
			//now res the is number of combs (choose j from countActBits)
			comb.add(resu);
			numInTotal += resu;
		}
		Double maxTry = numInTotal * ratioOfTrials;
		if(trySeeing > maxTry){
			trySeeing = maxTry.intValue();
		}
		if(!ifMultiLayer && numOfIte > numInTotal){
			numOfIte = numInTotal.intValue();
		}
		//now cal the marginal for random policy
		double marRandom = 0;
		for(int k = 1; k <= s._nMaxNondefActions; k ++){
			marRandom += Double.valueOf(k) / countActBits * comb.get(k) / numInTotal;
		}
		
		for(PVAR_NAME p: s._alActionNames){
			if(p._sPVarName.equals("move-up")){
				marRandom = 0.25;
				ifOldEle = true;
				break;
			}
		}
		
		for(PVAR_NAME p: s._alActionNames){
			if(p._sPVarName.equals("close-door")){
				marRandom = 0.2;
				ifNewEle = true;
				break;
			}
		}
		
		randomAction = marRandom;
		
		//initialize action prob
		ArrayList<Double> actionProb = null;
		
		
		
		TreeExp F = BuildF(s);
		
		
		actionProb = UpdateAllwtProj(s, F);
		/*
		Scanner sc = new Scanner(System.in);
		for(int i = 0; i < 14; i ++){
			double arbitary = sc.nextFloat();
			bestNumAct.set(i, arbitary);
		}
		*/
		//get final action
		
		/*
		System.out.println("\nFinally we are using the action probs: ");
		for(PVAR_NAME p: s._alActionNames){
			for(ArrayList<LCONST> t: s.generateAtoms(p)){
				System.out.println(p sd robWithName.get(p).get(t));
			}
		}
		*/
		if(ifRecordRoutine){
			System.out.println("Routine records:");
			System.out.println(bestNumAct);
			System.out.println(highestScore);
		}
		if(!ifRecordRoutine){
			actions = SampleAction(actionProb, s, false, true);
		}
		else{
			actions = SampleAction(s);
		}
		

		
		return actions;
	}

}
