package com.kcsl.ddresolver;

import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasHashSet;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.query.Attr;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.java.core.script.Common;
import com.ensoftcorp.open.cg.analysis.RapidTypeAnalysis;
import com.ensoftcorp.open.cg.analysis.ReallyRapidTypeAnalysis;
import com.ensoftcorp.open.cg.analysis.ZeroControlFlowAnalysis;
import com.ensoftcorp.open.java.commons.analysis.CallSiteAnalysis;
import com.ensoftcorp.open.java.commons.analysis.SetDefinitions;

public class Resolver {

	public static AtlasSet<Node> resolveCHA(){
		return resolveCHA(SetDefinitions.app());
	}
	
	public static AtlasSet<Node> resolveCHA(Q context){
		AtlasSet<Node> resolvableCallsites = new AtlasHashSet<Node>();
		
		Q candidates = context.nodes(XCSG.Method).difference(
				context.nodesTaggedWithAny(XCSG.Constructor, XCSG.privateVisibility, Attr.Node.IS_STATIC),
				context.methods("<init>"), context.methods("<clinit>"));

		Q candidateCallsites = CallSiteAnalysis.getMethodCallSites(candidates);
		
		for(Node callsite : candidateCallsites.eval().nodes()){
			AtlasSet<Node> callsiteTargets = CallSiteAnalysis.getTargetMethods(callsite);
			if(callsiteTargets.size() == 1){
				resolvableCallsites.add(callsite);
				
//				Q identityPassedToEdges = Common.edges(XCSG.IdentityPassedTo);
//				Q typeOfEdges = Common.edges(XCSG.TypeOf);
//				Q identityPassed = identityPassedToEdges.predecessors(Common.toQ(callsite));
//				Q identityPassedType = typeOfEdges.successors(identityPassed);
				
//				write: <identityPassedType>.callsite(ref, <params>)
			}
		}

		return resolvableCallsites;
	}
	
	public static AtlasSet<Node> resolveRRTA(){
		return resolveRRTA(SetDefinitions.app());
	}
	
	public static AtlasSet<Node> resolveRRTA(Q context){
		AtlasSet<Node> resolvableCallsites = new AtlasHashSet<Node>();
		
		Q candidates = context.nodes(XCSG.Method).difference(
				context.nodesTaggedWithAny(XCSG.Constructor, XCSG.privateVisibility, Attr.Node.IS_STATIC),
				context.methods("<init>"), context.methods("<clinit>"));

		Q candidateCallsites = CallSiteAnalysis.getMethodCallSites(candidates);
		
		for(Node callsite : candidateCallsites.eval().nodes()){
			Q rtaPerControlFlowEdges = Common.universe().edges(ReallyRapidTypeAnalysis.PER_CONTROL_FLOW);
			Q targetMethods = rtaPerControlFlowEdges.successors(Common.toQ(callsite));
			if(targetMethods.eval().nodes().size() == 1){
				resolvableCallsites.add(callsite);
			}
		}

		return resolvableCallsites;
	}
	
	public static AtlasSet<Node> resolveRTA(){
		return resolveRTA(SetDefinitions.app());
	}
	
	public static AtlasSet<Node> resolveRTA(Q context){
		AtlasSet<Node> resolvableCallsites = new AtlasHashSet<Node>();
		
		Q candidates = context.nodes(XCSG.Method).difference(
				context.nodesTaggedWithAny(XCSG.Constructor, XCSG.privateVisibility, Attr.Node.IS_STATIC),
				context.methods("<init>"), context.methods("<clinit>"));

		Q candidateCallsites = CallSiteAnalysis.getMethodCallSites(candidates);
		
		for(Node callsite : candidateCallsites.eval().nodes()){
			Q rtaPerControlFlowEdges = Common.universe().edges(RapidTypeAnalysis.PER_CONTROL_FLOW);
			Q targetMethods = rtaPerControlFlowEdges.successors(Common.toQ(callsite));
			if(targetMethods.eval().nodes().size() == 1){
				resolvableCallsites.add(callsite);
			}
		}

		return resolvableCallsites;
	}
	
//	public static long resolveXTA(){
//		return resolveXTA(SetDefinitions.app());
//	}
//	
//	public static long resolveXTA(Q context){
//		long resolvableCallsites = 0;
//		
//		Q candidates = context.nodes(XCSG.Method).difference(
//				context.nodesTaggedWithAny(XCSG.Constructor, XCSG.privateVisibility, Attr.Node.IS_STATIC),
//				context.methods("<init>"), context.methods("<clinit>"));
//
//		Q candidateCallsites = CallSiteAnalysis.getMethodCallSites(candidates);
//		
//		for(Node callsite : candidateCallsites.eval().nodes()){
//			Q xtaPerControlFlowEdges = Common.universe().edges(ClassicHybridTypeAnalysis.PER_CONTROL_FLOW);
//			Q targetMethods = xtaPerControlFlowEdges.successors(Common.toQ(callsite));
//			if(targetMethods.eval().nodes().size() == 1){
//				resolvableCallsites++;
//			}
//		}
//
//		return resolvableCallsites;
//	}
//	
//	public static long resolveXTA2(){
//		return resolveXTA2(SetDefinitions.app());
//	}
//	
//	public static long resolveXTA2(Q context){
//		long resolvableCallsites = 0;
//		
//		Q candidates = context.nodes(XCSG.Method).difference(
//				context.nodesTaggedWithAny(XCSG.Constructor, XCSG.privateVisibility, Attr.Node.IS_STATIC),
//				context.methods("<init>"), context.methods("<clinit>"));
//
//		Q candidateCallsites = CallSiteAnalysis.getMethodCallSites(candidates);
//		
//		for(Node callsite : candidateCallsites.eval().nodes()){
//			Q xtaPerControlFlowEdges = Common.universe().edges(HybridTypeAnalysis.PER_CONTROL_FLOW);
//			Q targetMethods = xtaPerControlFlowEdges.successors(Common.toQ(callsite));
//			if(targetMethods.eval().nodes().size() == 1){
//				resolvableCallsites++;
//			}
//		}
//
//		return resolvableCallsites;
//	}
	
	public static AtlasSet<Node> resolve0CFA(){
		return resolve0CFA(SetDefinitions.app());
	}
	
	public static AtlasSet<Node> resolve0CFA(Q context){
		AtlasSet<Node> resolvableCallsites = new AtlasHashSet<Node>();
		
		Q candidates = context.nodes(XCSG.Method).difference(
				context.nodesTaggedWithAny(XCSG.Constructor, XCSG.privateVisibility, Attr.Node.IS_STATIC),
				context.methods("<init>"), context.methods("<clinit>"));

		Q candidateCallsites = CallSiteAnalysis.getMethodCallSites(candidates);
		
		for(Node callsite : candidateCallsites.eval().nodes()){
			Q zeroCFAPerControlFlowEdges = Common.universe().edges(ZeroControlFlowAnalysis.PER_CONTROL_FLOW);
			Q targetMethods = zeroCFAPerControlFlowEdges.successors(Common.toQ(callsite));
			if(targetMethods.eval().nodes().size() == 1){
				resolvableCallsites.add(callsite);
			}
		}

		return resolvableCallsites;
	}
	
}
