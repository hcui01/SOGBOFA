package rddl.policy;

import java.security.AllPermission;
import java.util.*;

import org.apache.xerces.impl.xpath.XPath.Step;

import rddl.AState;
import rddl.EvalException;
import rddl.RDDL;
import rddl.RDDL.*;
import rddl.State;
import rddl.parser.parser;

import rddl.RDDL.DOMAIN;
import rddl.RDDL.INSTANCE;
import rddl.RDDL.ENUM_TYPE_DEF;
import rddl.RDDL.LCONST;
import rddl.RDDL.LVAR;
import rddl.RDDL.PVARIABLE_DEF;
import rddl.RDDL.PVAR_INST_DEF;
import rddl.RDDL.PVAR_NAME;
import util.Permutation;

public class TreeSearch{
	public TreeSearch() {
		// TODO Auto-generated constructor stub
	}
	public TreeSearch(State s, Random r, INSTANCE ins, boolean ifS, boolean ifA, DOMAIN dom) throws EvalException{
		_rand = r;
		_instance = ins;
		ifAggS = ifS;
		ifAggA = ifA;
		inst = ins;
		domi = dom;
		root = new StateNode(null, s, 0);
		maxDepth = 0;
	}
	final double ipsinon = 0.5f;
	final double MAX_DOUBLE = 10000000000.0;
	final double RolloutRatio = 0.5f;
	final int numOfSample = 10;
	public Random _rand;
	public INSTANCE _instance;
	boolean ifAggS, ifAggA;
	public int maxDepth;
	INSTANCE inst;
	DOMAIN domi;
	StateNode root;
	int count = 0;
	int previousSize = -1;
	

	class Performance{			//record performance of each action
		public Performance(){
			accumPerformance = 0;
			tryNumber = 0;
			avgPerformance = 0;
			
		}
		public Performance(double acc, int num, double per, ActionNode a){
			accumPerformance = acc;
			tryNumber = num;
			avgPerformance = per;
			action = a;
		}
		public double accumPerformance;
		public int tryNumber;
		public double avgPerformance;
		public ActionNode action;
	};
	class ActionNode{
		public ArrayList<StateNode> children;
		public StateNode father;
		public ArrayList<PVAR_INST_DEF> action;
		int depth;
		int index;
		public ActionNode() {
			// TODO Auto-generated constructor stub
		}
		public ActionNode(StateNode f, ArrayList<PVAR_INST_DEF> a, int d, int ind){
			father = f;
			children = new ArrayList<TreeSearch.StateNode>();
			action = a;
			depth = d;
			index = ind;
		}
	}
	public class StateNode{
		public ArrayList<Performance> perfRec;
		public ArrayList<Double> stateUtility;
		public ActionNode father;
		public boolean ifCheckAll;
		public State state;
		public int bestChild;
		
		public RandomConcurrentPolicyIndex actionGen;
		
		int depth;
		public StateNode() {
			// TODO Auto-generated constructor stub
		}
		public StateNode(ActionNode f, State s, int d) throws EvalException{
			father = f;
			state  = s;
			perfRec = new ArrayList<TreeSearch.Performance>();
			ifCheckAll = false;
			actionGen = new RandomConcurrentPolicyIndex(s);
			depth = d;
			stateUtility = new ArrayList<Double>();
			bestChild = -1;
		}
		
	}
	//find the action to traverse
	ActionNode ChooseAct(StateNode s){
		/*
		if(s.depth == 0){
			for(Performance p: s.perfRec){
				if(p.action.action.size() > 0 && p.action.action.get(0)._sPredName._sPVarName.equals("move-current-dir")){
					return p.action;
				}
			}
		}
		*/
		double dice = _rand.nextDouble();
		//choose greedily best
		ActionNode returnNode = new ActionNode();
		if(dice < ipsinon){
			returnNode = s.perfRec.get(s.bestChild).action;
		}
		else{
			int randInt = _rand.nextInt(s.perfRec.size());
			returnNode = s.perfRec.get(randInt).action;
		}
		return returnNode;
	}
	//explore a new action node and do some simulation
	ActionNode Explore(StateNode s) throws EvalException{
		ArrayList<PVAR_INST_DEF> newAction = s.actionGen.getCAction(s.state);
		//maybe at this time supurisingly we found we already tried all actions
		//because although there are space left in alrady
		//they are all ilegal
		//then we keep traversing from this state node
		if(newAction.size() == 1 && newAction.get(0)._oValue.equals(false)){
			s.ifCheckAll = true;
			return FindNewNode(s);
		}
		//otherwise we do exporation
		else{
			if(s.actionGen.already.size() >= s.actionGen.possibleComb){
				s.ifCheckAll = true;
			}
			ActionNode returnNode = new ActionNode(s, newAction, s.depth, s.perfRec.size());
			s.perfRec.add(new Performance(0, 0, 0, returnNode));
			//now we need also store the imidiate reward for the state-action pair
			s.state.setPVariables(s.state._actions, newAction);
			double reward = ((Number)domi._exprReward.sample(new HashMap<LVAR,LCONST>(), 
					s.state, _rand)).doubleValue();
			s.stateUtility.add(reward);
			return returnNode;
		}
	}
	
	//update from action node a to root action
	void Update(double val, ActionNode a){
		while(true){
			//record the current best action and its performance of a's father
			int currentBest = a.father.bestChild;
			double currentBestPerf = -1;
			if(a.father.bestChild != -1){
				currentBestPerf = a.father.perfRec.get(a.father.bestChild).avgPerformance;
			}
			//calculate the new performance of a
			Performance curPerf = a.father.perfRec.get(a.index);
			curPerf.accumPerformance += val;
			curPerf.tryNumber ++;
			curPerf.avgPerformance = curPerf.accumPerformance / curPerf.tryNumber;
			//update bestchild of father node if needed
			if(a.father.bestChild == -1){
				a.father.bestChild = a.index;
			}
			else{
				if(a.index != a.father.bestChild && 
						curPerf.avgPerformance > currentBestPerf){
					a.father.bestChild = a.index;
				}
				else{
					if(a.index == a.father.bestChild && curPerf.avgPerformance < currentBestPerf){
						double maxScore = -MAX_DOUBLE;
						for(int i = 0 ; i < a.father.perfRec.size(); i ++){
						    if(a.father.perfRec.get(i).avgPerformance > maxScore){
						    	maxScore = a.father.perfRec.get(i).avgPerformance;
						    	a.father.bestChild = i;
						    }
						} 
					}
				}
			}
			if(a.depth == 0){
				break;
			}
			
			//now go back to fater, which is a state node, to cal the state reward
			StateNode s = a.father;
			val *= inst._dDiscount;
			val += s.stateUtility.get(a.index);
			a = s.father;
		}
	}
	
	double RolloutOnce(StateNode s, int horizon, double discount, DOMAIN domain) throws EvalException{
		RandomConcurrentPolicyIndex actionGen = new RandomConcurrentPolicyIndex(s.state);
		double accum_reward = 0;
		double cur_discount = 1;
		if(!ifAggS && !ifAggA){
		
			State tempS = new State();
			tempS = (State)DeepCloneUtil.deepClone(s.state);
			for(int h = 0; h < horizon; h++ ) {
				ArrayList<PVAR_INST_DEF> _randomAction = actionGen.getCActionDup(tempS);
				tempS.computeNextState(_randomAction, _rand);
				double reward = ((Number)domain._exprReward.sample(new HashMap<LVAR,LCONST>(), 
					tempS, _rand)).doubleValue();
				accum_reward += reward * cur_discount;
				cur_discount *= discount;
				tempS.advanceNextState();
			}
		}
		if(ifAggS && !ifAggA){
			AState tempS = new AState();
			tempS.init(s.state);
			for(int h = 0; h < horizon; h++ ) {
				ArrayList<PVAR_INST_DEF> _randomAction = actionGen.getCActionDup(tempS);
				tempS.computeNextState(_randomAction, _rand);
				double reward = ((Number)domain._exprReward.sample(new HashMap<LVAR,LCONST>(), 
					tempS, _rand)).doubleValue();
				accum_reward += reward * cur_discount;
				cur_discount *= discount;
				tempS.advanceNextState();
			}
		}
		if(ifAggS && ifAggA){
			AState tempS = new AState();
			tempS.init(s.state);
			for(int h = 0; h < horizon; h++ ) {
				ArrayList<PVAR_INST_DEF> _randomAction = actionGen.getAActionDup(tempS, numOfSample);
				tempS.computeNextState(_randomAction, _rand);
				double reward = ((Number)domain._exprReward.sample(new HashMap<LVAR,LCONST>(), 
					tempS, _rand)).doubleValue();
				accum_reward += reward * cur_discount;
				cur_discount *= discount;
				tempS.advanceNextState();
			}
		}
		return accum_reward;
	}
	
	double Simulate(ActionNode a) throws EvalException{
		//put the first state node child to a
		State newState = new State();
		newState = (State)DeepCloneUtil.deepClone(a.father.state);
		newState.computeNextState(a.action, _rand);
		newState.advanceNextState();
		StateNode newStateNode = new StateNode(a, newState, a.depth + 1);
		a.children.add(newStateNode);
		return RolloutOnce(newStateNode, (int)(_instance._nHorizon * RolloutRatio) - a.depth, inst._dDiscount, domi);
	}
	
	ActionNode FindNewNode(StateNode s) throws EvalException{
		ActionNode newNode = new ActionNode();
		//new pointer to store the stateNode pointer
		StateNode oriS = s;
		//new state used to push foward the state
		State tempS = new State();
		tempS = (State)DeepCloneUtil.deepClone(s.state);
		//iteratively traverse untill getting into a statenode which is not fully explored
		while(s.ifCheckAll){
			ActionNode actionNode = ChooseAct(s);
			/*
			if(actionNode.depth == 1 && actionNode.action.size() == 1 && actionNode.action.get(0)._sPredName._sPVarName.equals("open-door-going-up")
					&& actionNode.father.father.action.size() == 1 && actionNode.father.father.action.get(0)._sPredName._sPVarName.equals("move-current-dir")){
				int a = 1;
				System.out.println(tempS);
			}
			*/
			tempS.computeNextState(actionNode.action, _rand);
			tempS.advanceNextState();
			/*
			if(actionNode.depth == 1 && actionNode.action.size() == 1 && actionNode.action.get(0)._sPredName._sPVarName.equals("open-door-going-up")
					&& actionNode.father.father.action.size() == 1 && actionNode.father.father.action.get(0)._sPredName._sPVarName.equals("move-current-dir")){
				int a = 1;
				System.out.println(tempS);
			}
			*/
			//check each of the next state node to see if there is anyone equal to tempS
			boolean ifExistStateNode = false;
			for(StateNode childS: actionNode.children){
				if(childS.state.IfSame(tempS)){
					s = childS;
					ifExistStateNode = true;
					break;
				}
			}
			//if not exist simple add a new state node to the children of actionNode
			//and move s to the new State Node
			//Aprrarently now s points to a node whose ifCheckAll mark must be false
			if(!ifExistStateNode){
				//build a new state node as a child of actionNode
				State newState = new State();
				newState = (State)DeepCloneUtil.deepClone(tempS);
				StateNode newStateNode = new StateNode(actionNode, newState, actionNode.depth + 1);
				actionNode.children.add(newStateNode);
				s = newStateNode;
			}
		}
		maxDepth = s.depth;
		//at leaf now
		//get a new action nde
		newNode = Explore(s);
		//recover pointer
		root = oriS;
		return newNode;
	}
	
	void Traverse() throws EvalException{
		ActionNode newNode = FindNewNode(root);
		/*
		if(newNode.depth == 2 && newNode.father.father.action.size() > 0 && newNode.father.father.action.get(0)._sPredName._sPVarName.equals("move-current-dir") 
				&& newNode.father.father.father.father.action.size() > 0 && newNode.father.father.father.father.action.get(0)._sPredName._sPVarName.equals("close-door")){
			int a = 1;
		}
		*/
		//get the initial evaluation of the action node
		//at the same time add a new state node to its children
		double initialValue = Simulate(newNode);
		//update the path from a to root
		Update(initialValue, newNode);
		
	}
}
