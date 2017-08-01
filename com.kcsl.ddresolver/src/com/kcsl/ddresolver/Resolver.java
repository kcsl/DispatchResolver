package com.kcsl.ddresolver;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;

import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasHashSet;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.log.Log;
import com.ensoftcorp.atlas.core.query.Attr;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.java.core.script.Common;
import com.ensoftcorp.open.cg.analysis.ClassHierarchyAnalysis;
import com.ensoftcorp.open.cg.analysis.RapidTypeAnalysis;
import com.ensoftcorp.open.cg.analysis.ReallyRapidTypeAnalysis;
import com.ensoftcorp.open.cg.analysis.ZeroControlFlowAnalysis;
import com.ensoftcorp.open.cg.preferences.CallGraphPreferences;
import com.ensoftcorp.open.commons.filters.InvalidFilterParameterException;
import com.ensoftcorp.open.commons.filters.LoopChildFilter;
import com.ensoftcorp.open.java.commons.analysis.CallSiteAnalysis;
import com.ensoftcorp.open.java.commons.analysis.CommonQueries;
import com.ensoftcorp.open.java.commons.analysis.SetDefinitions;
import com.ensoftcorp.open.pointsto.preferences.PointsToPreferences;

public class Resolver {

	public static void resetPreferences(){
		PointsToPreferences.restoreDefaults();
		PointsToPreferences.setJavaPointsToAnalysisMode();
		PointsToPreferences.enabledPointsToAnalysis(true);
		
		CallGraphPreferences.restoreDefaults();
		CallGraphPreferences.enableReallyRapidTypeAnalysis(true);
		CallGraphPreferences.enableZeroCFAAnalysis(true);
	}
	
	public static void collectMetrics(File output) throws IOException, InvalidFilterParameterException{
		String projectName = Common.universe().nodes(XCSG.Project).eval().nodes().one().getAttr(XCSG.name).toString();
		Log.info("Starting to collect transformation metrics for "+projectName);
		long timer = System.currentTimeMillis();
		
		FileWriter fw = new FileWriter(output);
		
		// overall application statistics
		fw.write("Total Application Methods,");
		fw.write("Total Potentially Transformable Application Methods,"); // not static, private or a constructor
		fw.write("Total Potentially Transformable Application Method Callsites,");

		// callsites in loops
		fw.write("Callsites Inside Loops,");
		fw.write("Callsites Outside Loops,");
		
		// break down of each analysis
		fw.write("CHA Time,CHA CG Size (nodes),CHA CG Size (edges),CHA Rewrite,CHA Clone,CHA Unchanged,Should Be Static,");
		fw.write("RRTA Time,RRTA CG Size (nodes),RRTA CG Size (edges),RRTA Rewrite,RRTA Clone,RRTA Unchanged,Should Be Static,");
		fw.write("0CFA Time,0CFA CG Size (nodes),0CFA CG Size (edges),0CFA Rewrite,0CFA Clone,0CFA Unchanged,Should Be Static,");
		
		// rewrite or clone (transformable) methods
		fw.write("CHA,");
		fw.write("RRTA,");
		fw.write("0CFA,");
		fw.write("CHA/RRTA,");
		fw.write("CHA/0CFA,");
		fw.write("RRTA/0CFA,");
		fw.write("CHA/RRTA/0CFA,");
		
		// callsites with one target
		fw.write("c1CHA,");
		fw.write("c1RRTA,");
		fw.write("c10CFA,");
		fw.write("c1CHA/c1RRTA,");
		fw.write("c1CHA/c10CFA,");
		fw.write("c1RRTA/c10CFA,");
		fw.write("c1CHA/c1RRTA/c10CFA,");
		
		// callsites transformed inside loops
		fw.write("ctlCHA,");
		fw.write("ctlRRTA,");
		fw.write("ctlCFA\n");
		
		// general app stats
		Q context = SetDefinitions.app();
		Q applicationMethods = context.nodes(XCSG.Method);
		Q potentiallyTransformableMethods = context.nodes(XCSG.Method).difference(
				context.nodesTaggedWithAny(XCSG.Constructor, XCSG.privateVisibility, Attr.Node.IS_STATIC),
				context.methods("<init>"), context.methods("<clinit>"));
		Q potentiallyTransformableMethodCallsites = CallSiteAnalysis.getMethodCallSites(potentiallyTransformableMethods);
		
		// loops
		LoopChildFilter filter = new LoopChildFilter();
		Q callsitesInLoops = filter.filter(potentiallyTransformableMethodCallsites, new HashMap<String,Object>());
		Q callsitesOutsideLoops = potentiallyTransformableMethodCallsites.difference(callsitesInLoops);
		
		Q chaCG = ClassHierarchyAnalysis.getInstance(false).getCallGraph();
		Q rrtaCG = ReallyRapidTypeAnalysis.getInstance(false).getCallGraph();
		Q zerocfaCG = ZeroControlFlowAnalysis.getInstance(false).getCallGraph();
		
		timer = System.currentTimeMillis();
		// run tagging operations
		tagShouldBeStaticMethodsCHA(potentiallyTransformableMethods);
		tagMethodsCHA(potentiallyTransformableMethods);
		tagTransformableCallsitesCHA(potentiallyTransformableMethodCallsites);
		long chaTime = System.currentTimeMillis() - timer;
		
		timer = System.currentTimeMillis();
		tagShouldBeStaticMethodsRRTA(potentiallyTransformableMethods);
		tagMethodsRRTA(potentiallyTransformableMethods);
		tagTransformableCallsitesRRTA(potentiallyTransformableMethodCallsites);
		long rrtaTime = System.currentTimeMillis() - timer;
		
		timer = System.currentTimeMillis();
		tagShouldBeStaticMethods0CFA(potentiallyTransformableMethods);
		tagMethods0CFA(potentiallyTransformableMethods);
		tagTransformableCallsites0CFA(potentiallyTransformableMethodCallsites);
		long zcfaTime = System.currentTimeMillis() - timer;
		
		// transformable method breakdown
		Q chaRewrite = Common.universe().nodes("CHA-REWRITE");
		Q chaClone = Common.universe().nodes("CHA-CLONE");
		Q chaUnchanged = Common.universe().nodes("CHA-UNCHANGED");
		Q chaShouldBeStatic = Common.universe().nodes("CHA-SHOULD-BE-STATIC");
		
		Q rrtaRewrite = Common.universe().nodes("RRTA-REWRITE");
		Q rrtaClone = Common.universe().nodes("RRTA-CLONE");
		Q rrtaUnchanged = Common.universe().nodes("RRTA-UNCHANGED");
		Q rrtaShouldBeStatic = Common.universe().nodes("RRTA-SHOULD-BE-STATIC");
		
		Q zerocfaRewrite = Common.universe().nodes("0CFA-REWRITE");
		Q zerocfaClone = Common.universe().nodes("0CFA-CLONE");
		Q zerocfaUnchanged = Common.universe().nodes("0CFA-UNCHANGED");
		Q zerocfaShouldBeStatic = Common.universe().nodes("0CFA-SHOULD-BE-STATIC");
		
		// methods venn breakdown
		Q CHA = Common.universe().nodes("CHA-TRANSFORMABLE").difference(Common.universe().nodes("RRTA-TRANSFORMABLE", "0CFA-TRANSFORMABLE"));
		Q RRTA = Common.universe().nodes("RRTA-TRANSFORMABLE").difference(Common.universe().nodes("CHA-TRANSFORMABLE", "0CFA-TRANSFORMABLE"));
		Q CFA = Common.universe().nodes("0CFA-TRANSFORMABLE").difference(Common.universe().nodes("CHA-TRANSFORMABLE", "RRTA-TRANSFORMABLE"));
		Q CHARRTA = Common.universe().nodesTaggedWithAll("CHA-TRANSFORMABLE", "RRTA-TRANSFORMABLE").difference(Common.universe().nodes("0CFA-TRANSFORMABLE"));
		Q CHA0CFA = Common.universe().nodesTaggedWithAll("CHA-TRANSFORMABLE", "0CFA-TRANSFORMABLE").difference(Common.universe().nodes("RRTA-TRANSFORMABLE"));
		Q RRTA0CFA = Common.universe().nodesTaggedWithAll("RRTA-TRANSFORMABLE", "0CFA-TRANSFORMABLE").difference(Common.universe().nodes("CHA-TRANSFORMABLE"));
		Q CHARRTA0CFA = Common.universe().nodesTaggedWithAll("RRTA-TRANSFORMABLE", "0CFA-TRANSFORMABLE", "CHA-TRANSFORMABLE");
		
		// callsite venn with one target breakdown by algorithm
		Q c1CHA = Common.universe().nodes("CHA-CALLSITETRANSFORMABLE").difference(Common.universe().nodes("RRTA-CALLSITETRANSFORMABLE", "0CFA-CALLSITETRANSFORMABLE"));
		Q c1RRTA = Common.universe().nodes("RRTA-CALLSITETRANSFORMABLE").difference(Common.universe().nodes("CHA-CALLSITETRANSFORMABLE", "0CFA-CALLSITETRANSFORMABLE"));
		Q c10CFA = Common.universe().nodes("0CFA-CALLSITETRANSFORMABLE").difference(Common.universe().nodes("CHA-CALLSITETRANSFORMABLE", "RRTA-CALLSITETRANSFORMABLE"));
		Q c1CHAc1RRTA = Common.universe().nodesTaggedWithAll("CHA-CALLSITETRANSFORMABLE", "RRTA-CALLSITETRANSFORMABLE").difference(Common.universe().nodes("0CFA-CALLSITETRANSFORMABLE"));
		Q c1CHAc10CFA = Common.universe().nodesTaggedWithAll("CHA-CALLSITETRANSFORMABLE", "0CFA-CALLSITETRANSFORMABLE").difference(Common.universe().nodes("RRTA-CALLSITETRANSFORMABLE"));
		Q c1RRTAc10CFA = Common.universe().nodesTaggedWithAll("RRTA-CALLSITETRANSFORMABLE", "0CFA-CALLSITETRANSFORMABLE").difference(Common.universe().nodes("CHA-CALLSITETRANSFORMABLE"));
		Q c1CHAc1RRTAc10CFA = Common.universe().nodesTaggedWithAll("RRTA-CALLSITETRANSFORMABLE", "0CFA-CALLSITETRANSFORMABLE", "CHA-CALLSITETRANSFORMABLE");

		Q ctlCHA = Common.universe().nodes("CHA-CALLSITETRANSFORMABLE").intersection(callsitesInLoops);
		Q ctlRRTA = Common.universe().nodes("RRTA-CALLSITETRANSFORMABLE").intersection(callsitesInLoops);
		Q ctl0CFA = Common.universe().nodes("0CFA-CALLSITETRANSFORMABLE").intersection(callsitesInLoops);
		
		// write out the counts
		fw.write(applicationMethods.eval().nodes().size() + ",");
		fw.write(potentiallyTransformableMethods.eval().nodes().size() + ",");
		fw.write(potentiallyTransformableMethodCallsites.eval().nodes().size() + ",");

		fw.write(callsitesInLoops.eval().nodes().size() + ",");
		fw.write(callsitesOutsideLoops.eval().nodes().size() + ",");
		
		fw.write(chaTime + "," + chaCG.retainEdges().eval().nodes().size() + "," + chaCG.eval().edges().size() + "," + chaRewrite.eval().nodes().size() + "," + chaClone.eval().nodes().size() + "," + chaUnchanged.eval().nodes().size() + "," + chaShouldBeStatic.eval().nodes().size() + ",");
		fw.write(rrtaTime + "," + rrtaCG.retainEdges().eval().nodes().size() + "," + rrtaCG.eval().edges().size() + "," + rrtaRewrite.eval().nodes().size() + "," + rrtaClone.eval().nodes().size() + "," + rrtaUnchanged.eval().nodes().size() + "," + rrtaShouldBeStatic.eval().nodes().size() +",");
		fw.write(zcfaTime + "," + zerocfaCG.retainEdges().eval().nodes().size() + "," + zerocfaCG.eval().edges().size() + "," + zerocfaRewrite.eval().nodes().size() + "," + zerocfaClone.eval().nodes().size() + "," + zerocfaUnchanged.eval().nodes().size()+ "," + zerocfaShouldBeStatic.eval().nodes().size() + ",");
		
		fw.write(CHA.eval().nodes().size() + ",");
		fw.write(RRTA.eval().nodes().size() + ",");
		fw.write(CFA.eval().nodes().size() + ",");
		fw.write(CHARRTA.eval().nodes().size() + ",");
		fw.write(CHA0CFA.eval().nodes().size() + ",");
		fw.write(RRTA0CFA.eval().nodes().size() + ",");
		fw.write(CHARRTA0CFA.eval().nodes().size() + ",");

		fw.write(c1CHA.eval().nodes().size() + ",");
		fw.write(c1RRTA.eval().nodes().size() + ",");
		fw.write(c10CFA.eval().nodes().size() + ",");
		fw.write(c1CHAc1RRTA.eval().nodes().size() + ",");
		fw.write(c1CHAc10CFA.eval().nodes().size() + ",");
		fw.write(c1RRTAc10CFA.eval().nodes().size() + ",");
		fw.write(c1CHAc1RRTAc10CFA.eval().nodes().size() + ",");
		
		fw.write(ctlCHA.eval().nodes().size() + ",");
		fw.write(ctlRRTA.eval().nodes().size() + ",");
		fw.write(ctl0CFA.eval().nodes().size() + "\n");
		
		fw.close();
	}

	public static void tagShouldBeStaticMethodsCHA(Q candidateMethods){
		for(Node method : candidateMethods.eval().nodes()){
			Q type = Common.toQ(method).parent();
			Q superTypes = Common.edges(XCSG.Supertype).forward(type);
			
			// remove method because a direct recursion could still be written statically
			Q instanceMethods = superTypes.children().nodes(XCSG.InstanceMethod).difference(Common.toQ(method));
			Q methodCallsites = CommonQueries.localDeclarations(Common.toQ(method)).nodes(XCSG.DynamicDispatchCallSite);
			
			boolean shouldBeStatic = true;
			Q chaPerControlFlowEdges = Common.universe().edges(ClassHierarchyAnalysis.PER_CONTROL_FLOW);
			if(!CommonQueries.isEmpty(chaPerControlFlowEdges.successors(methodCallsites).intersection(instanceMethods))){
				shouldBeStatic = false;
			}
			
			Q instanceVariables = superTypes.children().nodes(XCSG.InstanceVariable);
			Q dataFlowEdges = Common.edges(XCSG.DataFlow_Edge);
			Q write = dataFlowEdges.between(CommonQueries.localDeclarations(Common.toQ(method)), instanceVariables);
			Q read = dataFlowEdges.between(instanceVariables, CommonQueries.localDeclarations(Common.toQ(method)));
			
			if(!CommonQueries.isEmpty(read) || !CommonQueries.isEmpty(write)){
				shouldBeStatic = false;
			}
			
			if(shouldBeStatic){
				method.tag("CHA-SHOULD-BE-STATIC");
			}
		}
	}
	
	public static void tagShouldBeStaticMethodsRRTA(Q candidateMethods){
		for(Node method : candidateMethods.eval().nodes()){
			Q type = Common.toQ(method).parent();
			Q superTypes = Common.edges(XCSG.Supertype).forward(type);
			
			// remove method because a direct recursion could still be written statically
			Q instanceMethods = superTypes.children().nodes(XCSG.InstanceMethod).difference(Common.toQ(method));
			Q methodCallsites = CommonQueries.localDeclarations(Common.toQ(method)).nodes(XCSG.DynamicDispatchCallSite);
			
			boolean shouldBeStatic = true;
			Q rrtaPerControlFlowEdges = Common.universe().edges(ReallyRapidTypeAnalysis.PER_CONTROL_FLOW);
			if(!CommonQueries.isEmpty(rrtaPerControlFlowEdges.successors(methodCallsites).intersection(instanceMethods))){
				shouldBeStatic = false;
			}
			
			Q instanceVariables = superTypes.children().nodes(XCSG.InstanceVariable);
			Q dataFlowEdges = Common.edges(XCSG.DataFlow_Edge);
			Q write = dataFlowEdges.between(CommonQueries.localDeclarations(Common.toQ(method)), instanceVariables);
			Q read = dataFlowEdges.between(instanceVariables, CommonQueries.localDeclarations(Common.toQ(method)));
			
			if(!CommonQueries.isEmpty(read) || !CommonQueries.isEmpty(write)){
				shouldBeStatic = false;
			}
			
			if(shouldBeStatic){
				method.tag("RRTA-SHOULD-BE-STATIC");
			}
		}
	}
	
	public static void tagShouldBeStaticMethods0CFA(Q candidateMethods){
		for(Node method : candidateMethods.eval().nodes()){
			Q type = Common.toQ(method).parent();
			Q superTypes = Common.edges(XCSG.Supertype).forward(type);
			
			// remove method because a direct recursion could still be written statically
			Q instanceMethods = superTypes.children().nodes(XCSG.InstanceMethod).difference(Common.toQ(method));
			Q methodCallsites = CommonQueries.localDeclarations(Common.toQ(method)).nodes(XCSG.DynamicDispatchCallSite);
			
			boolean shouldBeStatic = true;
			Q zerocfaPerControlFlowEdges = Common.universe().edges(ZeroControlFlowAnalysis.PER_CONTROL_FLOW);
			if(!CommonQueries.isEmpty(zerocfaPerControlFlowEdges.successors(methodCallsites).intersection(instanceMethods))){
				shouldBeStatic = false;
			}
			
			Q instanceVariables = superTypes.children().nodes(XCSG.InstanceVariable);
			Q dataFlowEdges = Common.edges(XCSG.DataFlow_Edge);
			Q write = dataFlowEdges.between(CommonQueries.localDeclarations(Common.toQ(method)), instanceVariables);
			Q read = dataFlowEdges.between(instanceVariables, CommonQueries.localDeclarations(Common.toQ(method)));
			
			if(!CommonQueries.isEmpty(read) || !CommonQueries.isEmpty(write)){
				shouldBeStatic = false;
			}
			
			if(shouldBeStatic){
				method.tag("0CFA-SHOULD-BE-STATIC");
			}
		}
	}
	
	public static void tagMethodsCHA(Q candidateMethods){
		Q chaPerControlFlowEdges = Common.universe().edges(ClassHierarchyAnalysis.PER_CONTROL_FLOW);
		for(Node method : candidateMethods.eval().nodes()){
			
			boolean allCallsitesHave1 = true;
			boolean hasCallsites = false;
			for(Node callsite : chaPerControlFlowEdges.predecessors(Common.toQ(method)).eval().nodes()){
				hasCallsites = true;
				Q targetMethods = chaPerControlFlowEdges.successors(Common.toQ(callsite));
				if(targetMethods.eval().nodes().size() != 1){
					allCallsitesHave1 = false;
				}
			}
			
			if(!hasCallsites){
				method.tag("CHA-UNCHANGED");
			} else {
				method.tag("CHA-TRANSFORMABLE");
				if(allCallsitesHave1){
					method.tag("CHA-REWRITE");
				} else {
					method.tag("CHA-CLONE");
				}
			}
		}
	}
	
	public static void tagMethodsRRTA(Q candidateMethods){
		Q rrtaPerControlFlowEdges = Common.universe().edges(ReallyRapidTypeAnalysis.PER_CONTROL_FLOW);
		for(Node method : candidateMethods.eval().nodes()){
			
			boolean allCallsitesHave1 = true;
			boolean hasCallsites = false;
			for(Node callsite : rrtaPerControlFlowEdges.predecessors(Common.toQ(method)).eval().nodes()){
				hasCallsites = true;
				Q targetMethods = rrtaPerControlFlowEdges.successors(Common.toQ(callsite));
				if(targetMethods.eval().nodes().size() != 1){
					allCallsitesHave1 = false;
				}
			}
			
			if(!hasCallsites){
				method.tag("RRTA-UNCHANGED");
			} else {
				method.tag("RRTA-TRANSFORMABLE");
				if(allCallsitesHave1){
					method.tag("RRTA-REWRITE");
				} else {
					method.tag("RRTA-CLONE");
				}
			}
		}
	}
	
	public static void tagMethods0CFA(Q candidateMethods){
		Q zerocfaPerControlFlowEdges = Common.universe().edges(ZeroControlFlowAnalysis.PER_CONTROL_FLOW);
		for(Node method : candidateMethods.eval().nodes()){
			
			boolean allCallsitesHave1 = true;
			boolean hasCallsites = false;
			for(Node callsite : zerocfaPerControlFlowEdges.predecessors(Common.toQ(method)).eval().nodes()){
				hasCallsites = true;
				Q targetMethods = zerocfaPerControlFlowEdges.successors(Common.toQ(callsite));
				if(targetMethods.eval().nodes().size() != 1){
					allCallsitesHave1 = false;
				}
			}
			
			if(!hasCallsites){
				method.tag("0CFA-UNCHANGED");
			} else {
				method.tag("0CFA-TRANSFORMABLE");
				if(allCallsitesHave1){
					method.tag("0CFA-REWRITE");
				} else {
					method.tag("0CFA-CLONE");
				}
			}
		}
	}
	
	public static void tagTransformableCallsitesCHA(Q candidateCallsites){
		for(Node callsite : candidateCallsites.eval().nodes()){
			Q chaPerControlFlowEdges = Common.universe().edges(ClassHierarchyAnalysis.PER_CONTROL_FLOW);
			Q targetMethods = chaPerControlFlowEdges.successors(Common.toQ(callsite));
			if(targetMethods.eval().nodes().size() == 1){
				callsite.tag("CHA-CALLSITETRANSFORMABLE");
			}
		}
	}
	
	public static void tagTransformableCallsitesRRTA(Q candidateCallsites){
		for(Node callsite : candidateCallsites.eval().nodes()){
			Q rtaPerControlFlowEdges = Common.universe().edges(ReallyRapidTypeAnalysis.PER_CONTROL_FLOW);
			Q targetMethods = rtaPerControlFlowEdges.successors(Common.toQ(callsite));
			if(targetMethods.eval().nodes().size() == 1){
				callsite.tag("RRTA-CALLSITETRANSFORMABLE");
			}
		}
	}
	
	public static void tagTransformableCallsites0CFA(Q candidateCallsites){
		for(Node callsite : candidateCallsites.eval().nodes()){
			Q zerocfaPerControlFlowEdges = Common.universe().edges(ZeroControlFlowAnalysis.PER_CONTROL_FLOW);
			Q targetMethods = zerocfaPerControlFlowEdges.successors(Common.toQ(callsite));
			if(targetMethods.eval().nodes().size() == 1){
				callsite.tag("0CFA-CALLSITETRANSFORMABLE");
			}
		}
	}
	
}
