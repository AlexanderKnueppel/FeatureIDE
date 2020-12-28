/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.featurehouse.proofautomation.excel;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.List;

import org.apache.poi.ss.usermodel.*;
import org.apache.poi.ss.util.WorkbookUtil;
import org.apache.poi.xssf.usermodel.XSSFRow;
import org.apache.poi.xssf.usermodel.XSSFSheet;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;

import de.ovgu.featureide.core.featurehouse.proofautomation.evaluation.CompleteApproachesEvaluation;
import de.ovgu.featureide.core.featurehouse.proofautomation.evaluation.ApproachData;
import de.ovgu.featureide.core.featurehouse.proofautomation.evaluation.ProofStats;
import de.ovgu.featureide.core.featurehouse.proofautomation.evaluation.SingleApproachEvaluation;
import de.ovgu.featureide.core.featurehouse.proofautomation.statistics.ProofInformation;
import de.ovgu.featureide.core.featurehouse.proofautomation.statistics.ProofStatistics;



/**
 * Saves the evaluation in excel files 
 * 
 * @author Stefanie
 */
public class ExcelManager2 {	
	
	public static void generateAllApproachWithInitSeperated(CompleteApproachesEvaluation c){
		Workbook wb = new XSSFWorkbook();
		CreationHelper crHelper = wb.getCreationHelper();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    Row curRow = fullEvaluationTitles(total,crHelper,8);
	    fullOptionTitles(curRow,crHelper,1);   
	    Sheet initialEffort = wb.createSheet(WorkbookUtil.createSafeSheetName("Initial Effort"));
	    fullEvaluationTitles(initialEffort,crHelper,1);
	    int rowcounter = 2;
	    for(ApproachData e: c.getAllApproaches()){
	    	SingleApproachEvaluation s = getInitialProject(e);
	    	ProofStatistics reuse = new ProofStatistics();
		    reuse.addStatistics(e.firstPhaseReuse);
		    reuse.removeStatistics(s.firstPhaseReuse);
		    reuse.addStatistics(e.secondPhaseReuse);
		    reuse.removeStatistics(s.secondPhaseReuse);
		    ProofStatistics stat = new ProofStatistics();
		    stat.addStatistics(e.firstPhase);
		    stat.removeStatistics(s.firstPhase);
		    stat.addStatistics(e.secondPhase);
		    stat.removeStatistics(s.secondPhase);
	    	Row totalCurRow = proofLists(8,total,crHelper, e.evaluatePath.getName(),reuse,stat, rowcounter,e.failedProofs-s.failedProofs,e.proofs-s.proofs);
	    	addOptions(1,crHelper, totalCurRow,e);
	    	ProofStatistics initReuse = s.firstPhaseReuse;
	    	initReuse.addStatistics(s.secondPhaseReuse);
	    	ProofStatistics initStat = s.firstPhase;
	    	initStat.addStatistics(s.secondPhase);
	    	proofLists(1,initialEffort,crHelper,e.evaluatePath.getName(),initReuse,initStat,rowcounter,s.failedProofs,s.proofs);
	    	rowcounter++;
	    }
	    autosizeColumns(total,20);
	    autosizeColumns(initialEffort,9);
	    try {
	    	FileOutputStream fOut = new FileOutputStream(new File(c.evaluatePath.getAbsolutePath()+System.getProperty("file.separator")+"Evaluation Results with Initial Effort.xlsx"));
			wb.write(fOut);
			fOut.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	    try {
			wb.close();
		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}
	
	public static SingleApproachEvaluation getInitialProject(ApproachData e){
		for(SingleApproachEvaluation s: e.getProjectVersion()){
			if(s.evaluatePath.getName().contains("1")){
				return s;
			}
		}
		return null;
	}
	/**
	 * Generates a summary of all approaches in an xlsx file
	 * @param c
	 */
	public static void generateAllApproachEvaluationWithReuseXLS(CompleteApproachesEvaluation c){
		Workbook wb = new XSSFWorkbook();
		CreationHelper crHelper = wb.getCreationHelper();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    Row curRow = fullEvaluationTitles(total,crHelper,8);
	    fullOptionTitles(curRow,crHelper,1);
	    Sheet phaseOne = wb.createSheet(WorkbookUtil.createSafeSheetName("First Phase"));
	    fullEvaluationTitles(phaseOne,crHelper,1);
	    Sheet phaseTwo = wb.createSheet(WorkbookUtil.createSafeSheetName("Second Phase"));
	    fullEvaluationTitles(phaseTwo,crHelper,1);	    
	    int rowcounter = 2;
	    for(ApproachData e: c.getAllApproaches()){
	    	ProofStatistics reuse = new ProofStatistics();
		    reuse.addStatistics(e.firstPhaseReuse);
		    reuse.addStatistics(e.secondPhaseReuse);
		    ProofStatistics stat = new ProofStatistics();
		    stat.addStatistics(e.firstPhase);
		    stat.addStatistics(e.secondPhase);
	    	Row totalCurRow = proofLists(8,total,crHelper, e.evaluatePath.getName(),reuse,stat, rowcounter,e.failedProofs,e.proofs);
	    	addOptions(1,crHelper, totalCurRow,e);
	    	proofLists(1,phaseOne,crHelper, e.evaluatePath.getName(),e.firstPhaseReuse,e.firstPhase, rowcounter,e.failedProofs,e.proofs);
	    	proofLists(1,phaseTwo,crHelper, e.evaluatePath.getName(),e.secondPhaseReuse,e.secondPhase, rowcounter,e.failedProofs,e.proofs);
	    	rowcounter++;
	    }
	    autosizeColumns(total,20);
	    autosizeColumns(phaseOne,9);
	    autosizeColumns(phaseTwo,9);
	    try {
	    	FileOutputStream fOut = new FileOutputStream(c.statistics);
			wb.write(fOut);
			fOut.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	    try {
			wb.close();
		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}
	
	
	private static void addOptions(int firstColumn,CreationHelper crHelper, Row curRow,ApproachData e){
		int version = e.getVersionNumber();
		//Feature-based Phase
		if(version==1){
			curRow.createCell(firstColumn).setCellValue(1);
		}
		else{
			curRow.createCell(firstColumn).setCellValue(0);
		}
		//Abstract Contracts
		if(version==1||version==2||version==7){
			curRow.createCell(firstColumn+1).setCellValue(1);
		}
		else{
			curRow.createCell(firstColumn+1).setCellValue(0);
		}
		//Method Call Treatment
		if(version==1||version==2||version==3||version==7||version==8){
			curRow.createCell(firstColumn+2).setCellValue(crHelper.createRichTextString("Contracting"));;
		}
		else{
			curRow.createCell(firstColumn+2).setCellValue(crHelper.createRichTextString("Inlining"));;
		}
		//MetaProduct Generation
		if(version==1||version==2||version==3||version==4||version==9){
			curRow.createCell(firstColumn+3).setCellValue(crHelper.createRichTextString("With Dispatcher"));
		}
		else{
			curRow.createCell(firstColumn+3).setCellValue(crHelper.createRichTextString("Without Dispatcher"));
		}
		//Proof Replay Feature Phase
		if(version==1){
			curRow.createCell(firstColumn+4).setCellValue(1);
		}
		else{
			curRow.createCell(firstColumn+4).setCellValue(0);
		}
		//Proof Replay FAM Phase
		if(version==2||version==3||version==4||version==6||version==7||version==8){
			curRow.createCell(firstColumn+5).setCellValue(1);
		}
		else{
			curRow.createCell(firstColumn+5).setCellValue(0);
		}
		//Assignable
		if(version==1||version==2||version==3||version==4||version==5||version==6||version==7||version==8||version==9){
			curRow.createCell(firstColumn+6).setCellValue(1);
		}
		else{
			curRow.createCell(firstColumn+6).setCellValue(0);
		}
	}
	
	private static Row proofLists(int firstColumn, Sheet s, CreationHelper crHelper, String name, ProofStatistics reuse, ProofStatistics stat, int rowcounter,int failedProofs, int succededProofs){
		Row approachRow = s.createRow(rowcounter);
    	approachRow.createCell(firstColumn).setCellValue(crHelper.createRichTextString(name));
    	approachRow.createCell(firstColumn+1).setCellValue(reuse.getNodes());
    	approachRow.createCell(firstColumn+2).setCellValue(reuse.getBranches());
    	approachRow.createCell(firstColumn+3).setCellValue(reuse.getAppliedRules());
    	approachRow.createCell(firstColumn+4).setCellValue(reuse.getAutomodeTime());
    	approachRow.createCell(firstColumn+5).setCellValue(stat.getNodes());
    	approachRow.createCell(firstColumn+6).setCellValue(stat.getBranches());
    	approachRow.createCell(firstColumn+7).setCellValue(stat.getAppliedRules());
    	approachRow.createCell(firstColumn+8).setCellValue(stat.getAutomodeTime());
    	if(s.getSheetName().equals("Total")||s.getSheetName().equals("Initial Effort")){
    		approachRow.createCell(firstColumn+9).setCellValue(crHelper.createRichTextString((succededProofs-failedProofs)+"\\"+succededProofs));
    	}
    	return approachRow;
	}
	private static Row fullEvaluationTitles(Sheet s, CreationHelper crHelper, int start){
		Row firstRow = s.createRow(0);
	    firstRow.createCell(0).setCellValue(crHelper.createRichTextString("Evolution"));
		Row secondRow = s.createRow(1);
	    secondRow.createCell(start).setCellValue(crHelper.createRichTextString("Approach"));
	    secondRow.createCell(start+1).setCellValue(crHelper.createRichTextString("Reused Proof Steps"));
	    secondRow.createCell(start+2).setCellValue(crHelper.createRichTextString("Reused Branches"));
	    secondRow.createCell(start+3).setCellValue(crHelper.createRichTextString("Reused Applied Rules"));
	    secondRow.createCell(start+4).setCellValue(crHelper.createRichTextString("ReusedProof Time"));
	    secondRow.createCell(start+5).setCellValue(crHelper.createRichTextString("Proof Steps"));
	    secondRow.createCell(start+6).setCellValue(crHelper.createRichTextString("Branches"));
	    secondRow.createCell(start+7).setCellValue(crHelper.createRichTextString("Applied Rules"));
	    secondRow.createCell(start+8).setCellValue(crHelper.createRichTextString("Proof Time"));
	    if(s.getSheetName().equals("Total")){
	    	secondRow.createCell(start+9).setCellValue(crHelper.createRichTextString("Closed Proofs"));
	    }
	    return secondRow;
	}
	
	private static void fullOptionTitles(Row secondRow, CreationHelper crHelper,int start){
	    secondRow.createCell(start).setCellValue(crHelper.createRichTextString("Feature-based Phase"));
	    secondRow.createCell(start+1).setCellValue(crHelper.createRichTextString("Abstract Contracts"));
	    secondRow.createCell(start+2).setCellValue(crHelper.createRichTextString("Method Call Treatment"));
	    secondRow.createCell(start+3).setCellValue(crHelper.createRichTextString("Meta-Product Generation"));
	    secondRow.createCell(start+4).setCellValue(crHelper.createRichTextString("Proof Replay FEATURE"));
	    secondRow.createCell(start+5).setCellValue(crHelper.createRichTextString("Proof Replay FAM"));
	    secondRow.createCell(start+6).setCellValue(crHelper.createRichTextString("Assignable"));
	}
	
	
	public static void generateSingleApproachEvaluationWithReuseXLS(ApproachData approachData){
		Workbook wb = new XSSFWorkbook();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    CreationHelper crHelper = wb.getCreationHelper();
	    createMethodSheet(wb,crHelper,approachData.getAllDisjointProofs());
	    Row firstRow = total.createRow(0);
	    firstRow.createCell(0).setCellValue(crHelper.createRichTextString("Evolution"));
	    firstRow.createCell(2).setCellValue(crHelper.createRichTextString("Reused Proof Steps"));
	    firstRow.createCell(3).setCellValue(crHelper.createRichTextString("Reused Branches"));
	    firstRow.createCell(4).setCellValue(crHelper.createRichTextString("Reused Applied Rules"));
	    firstRow.createCell(5).setCellValue(crHelper.createRichTextString("Reused Proof Time"));
	    firstRow.createCell(6).setCellValue(crHelper.createRichTextString("Proof Steps"));
	    firstRow.createCell(7).setCellValue(crHelper.createRichTextString("Branches"));
	    firstRow.createCell(8).setCellValue(crHelper.createRichTextString("Applied Rules"));
	    firstRow.createCell(9).setCellValue(crHelper.createRichTextString("Proof Time"));
	    firstRow.createCell(10).setCellValue(crHelper.createRichTextString("Proof Closed"));
	    int rowcounter = 1;
	    for(SingleApproachEvaluation s: approachData.getProjectVersion()){
	    	Sheet currentProject = wb.createSheet(WorkbookUtil.createSafeSheetName(s.evaluatePath.getName()));
	    	createColumnTitles(currentProject,crHelper);
	    	int rowcount = 1;
		    rowcount = createProofListsForApproach(s.getProofList(),currentProject,crHelper,rowcount);
		    createLastRowForApproach(s.secondPhaseReuse,s.secondPhase,currentProject,crHelper,rowcount,"Total",s);
		    autosizeColumns(currentProject,11);
	    }
	    for(SingleApproachEvaluation s : approachData.getProjectVersion()){
	    	Row appraochRow = total.createRow(rowcounter);
	    	appraochRow.createCell(1).setCellValue(crHelper.createRichTextString(s.evaluatePath.getName()));
	    	appraochRow.createCell(2).setCellValue(s.secondPhaseReuse.getNodes());
	    	appraochRow.createCell(3).setCellValue(s.secondPhaseReuse.getBranches());
	    	appraochRow.createCell(4).setCellValue(s.secondPhaseReuse.getAppliedRules());
	    	appraochRow.createCell(5).setCellValue(s.secondPhaseReuse.getAutomodeTime());
	    	appraochRow.createCell(6).setCellValue(s.secondPhase.getNodes());
	    	appraochRow.createCell(7).setCellValue(s.secondPhase.getBranches());
	    	appraochRow.createCell(8).setCellValue(s.secondPhase.getAppliedRules());
	    	appraochRow.createCell(9).setCellValue(s.secondPhase.getAutomodeTime());
	    	appraochRow.createCell(10).setCellValue(crHelper.createRichTextString((s.proofs-s.failedProofs)+"\\"+s.proofs));
	    	rowcounter++;
	    }
	    Row totalTwoRow = total.createRow(rowcounter);
	    totalTwoRow.createCell(0).setCellValue(crHelper.createRichTextString("Total"));
	    totalTwoRow.createCell(2).setCellValue(approachData.secondPhaseReuse.getNodes());
	    totalTwoRow.createCell(3).setCellValue(approachData.secondPhaseReuse.getBranches());
	    totalTwoRow.createCell(4).setCellValue(approachData.secondPhaseReuse.getAppliedRules());
	    totalTwoRow.createCell(5).setCellValue(approachData.secondPhaseReuse.getAutomodeTime());
	    totalTwoRow.createCell(6).setCellValue(approachData.secondPhase.getNodes());
	    totalTwoRow.createCell(7).setCellValue(approachData.secondPhase.getBranches());
	    totalTwoRow.createCell(8).setCellValue(approachData.secondPhase.getAppliedRules());
	    totalTwoRow.createCell(9).setCellValue(approachData.secondPhase.getAutomodeTime());
	    totalTwoRow.createCell(10).setCellValue(crHelper.createRichTextString((approachData.proofs-approachData.failedProofs)+"\\"+approachData.proofs));
	    autosizeColumns(total,10);
	    try {
	    	FileOutputStream fOut = new FileOutputStream(approachData.statistics);
			wb.write(fOut);
			fOut.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	    try {
			wb.close();
		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}
	
	public static void generateSingleApproachTwoPhaseEvaluationWithReuseXLS(ApproachData ep){
		Workbook wb = new XSSFWorkbook();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    CreationHelper crHelper = wb.getCreationHelper();
	    createMethodSheet(wb,crHelper,ep.getAllDisjointProofs());
	    Row firstRow = total.createRow(0);
	    firstRow.createCell(0).setCellValue(crHelper.createRichTextString("Evolution"));
	    firstRow.createCell(2).setCellValue(crHelper.createRichTextString("Reused Proof Steps"));
	    firstRow.createCell(3).setCellValue(crHelper.createRichTextString("Reused Branches"));
	    firstRow.createCell(4).setCellValue(crHelper.createRichTextString("Reused Applied Rules"));
	    firstRow.createCell(5).setCellValue(crHelper.createRichTextString("Reused Proof Time"));
	    firstRow.createCell(6).setCellValue(crHelper.createRichTextString("Proof Steps"));
	    firstRow.createCell(7).setCellValue(crHelper.createRichTextString("Branches"));
	    firstRow.createCell(8).setCellValue(crHelper.createRichTextString("Applied Rules"));
	    firstRow.createCell(9).setCellValue(crHelper.createRichTextString("Proof Time"));
	    firstRow.createCell(10).setCellValue(crHelper.createRichTextString("Proof Closed"));
	    Row secondRow = total.createRow(1);
	    secondRow.createCell(0).setCellValue(crHelper.createRichTextString("First Phase"));
	    int rowcounter = 2;
	    int countProjects = 0;
	    for(SingleApproachEvaluation s: ep.getProjectVersion()){
	    	Sheet currentProject = wb.createSheet(WorkbookUtil.createSafeSheetName(s.evaluatePath.getName()));
	    	createColumnTitles(currentProject,crHelper);
	    	int rowcount = 1;
    		Row phaseRow = currentProject.createRow(rowcount);
    		phaseRow.createCell(0).setCellValue(crHelper.createRichTextString("First Phase"));
    		rowcount++;
    		rowcount = createProofListsForApproach(s.getPhase1ProofList(),currentProject,crHelper,rowcount);
    		createLastRowForApproach(s.firstPhaseReuse,s.firstPhase,currentProject,crHelper,rowcount,"First Phase Total",s);
    		rowcount++;
    		phaseRow = currentProject.createRow(rowcount);
    		phaseRow.createCell(0).setCellValue(crHelper.createRichTextString("Second Phase"));
    		rowcount++;
		    rowcount = createProofListsForApproach(s.getProofList(),currentProject,crHelper,rowcount);
		    createLastRowForApproach(s.secondPhaseReuse,s.secondPhase,currentProject,crHelper,rowcount,"Second Phase Total",s);
		    rowcount++;
		    ProofStatistics reuseSum = new ProofStatistics();
		    reuseSum.addStatistics(s.firstPhaseReuse);
		    reuseSum.addStatistics(s.secondPhaseReuse);
		    ProofStatistics sum = new ProofStatistics();
		    sum.addStatistics(s.firstPhase);
		    sum.addStatistics(s.secondPhase);
		    createLastRowForApproach(reuseSum,sum,currentProject,crHelper,rowcount,"Total",s);
		    autosizeColumns(currentProject,11);
		    countProjects++;
	    }
	    Row totalOneRow = total.createRow(rowcounter+countProjects);
	    totalOneRow.createCell(0).setCellValue(crHelper.createRichTextString("Total First Phase"));
	    totalOneRow.createCell(2).setCellValue(ep.firstPhaseReuse.getNodes());
	    totalOneRow.createCell(3).setCellValue(ep.firstPhaseReuse.getBranches());
	    totalOneRow.createCell(4).setCellValue(ep.firstPhaseReuse.getAppliedRules());
	    totalOneRow.createCell(5).setCellValue(ep.firstPhaseReuse.getAutomodeTime());
	    totalOneRow.createCell(6).setCellValue(ep.firstPhase.getNodes());
	    totalOneRow.createCell(7).setCellValue(ep.firstPhase.getBranches());
	    totalOneRow.createCell(8).setCellValue(ep.firstPhase.getAppliedRules());
	    totalOneRow.createCell(9).setCellValue(ep.firstPhase.getAutomodeTime());
	    Row afterRow = total.createRow(rowcounter+countProjects+1);
	    afterRow.createCell(0).setCellValue(crHelper.createRichTextString("Second Phase"));
	    for(SingleApproachEvaluation s : ep.getProjectVersion()){
	    	Row appraochRow = total.createRow(rowcounter);
	    	appraochRow.createCell(1).setCellValue(crHelper.createRichTextString(s.evaluatePath.getName()));
	    	appraochRow.createCell(2).setCellValue(s.firstPhaseReuse.getNodes());
	    	appraochRow.createCell(3).setCellValue(s.firstPhaseReuse.getBranches());
	    	appraochRow.createCell(4).setCellValue(s.firstPhaseReuse.getAppliedRules());
	    	appraochRow.createCell(5).setCellValue(s.firstPhaseReuse.getAutomodeTime());
	    	appraochRow.createCell(6).setCellValue(s.firstPhase.getNodes());
	    	appraochRow.createCell(7).setCellValue(s.firstPhase.getBranches());
	    	appraochRow.createCell(8).setCellValue(s.firstPhase.getAppliedRules());
	    	appraochRow.createCell(9).setCellValue(s.firstPhase.getAutomodeTime());
	    	appraochRow = total.createRow(rowcounter+countProjects+2);
	    	appraochRow.createCell(1).setCellValue(crHelper.createRichTextString(s.evaluatePath.getName()));
	    	appraochRow.createCell(2).setCellValue(s.secondPhaseReuse.getNodes());
	    	appraochRow.createCell(3).setCellValue(s.secondPhaseReuse.getBranches());
	    	appraochRow.createCell(4).setCellValue(s.secondPhaseReuse.getAppliedRules());
	    	appraochRow.createCell(5).setCellValue(s.secondPhaseReuse.getAutomodeTime());
	    	appraochRow.createCell(6).setCellValue(s.secondPhase.getNodes());
	    	appraochRow.createCell(7).setCellValue(s.secondPhase.getBranches());
	    	appraochRow.createCell(8).setCellValue(s.secondPhase.getAppliedRules());
	    	appraochRow.createCell(9).setCellValue(s.secondPhase.getAutomodeTime());
	    	appraochRow.createCell(10).setCellValue(crHelper.createRichTextString((s.proofs-s.failedProofs)+"\\"+s.proofs));
	    	rowcounter++;
	    }
	    Row totalTwoRow = total.createRow(rowcounter+countProjects+2);
	    totalTwoRow.createCell(0).setCellValue(crHelper.createRichTextString("Total Second Phase"));
	    totalTwoRow.createCell(2).setCellValue(ep.secondPhaseReuse.getNodes());
	    totalTwoRow.createCell(3).setCellValue(ep.secondPhaseReuse.getBranches());
	    totalTwoRow.createCell(4).setCellValue(ep.secondPhaseReuse.getAppliedRules());
	    totalTwoRow.createCell(5).setCellValue(ep.secondPhaseReuse.getAutomodeTime());
	    totalTwoRow.createCell(6).setCellValue(ep.secondPhase.getNodes());
	    totalTwoRow.createCell(7).setCellValue(ep.secondPhase.getBranches());
	    totalTwoRow.createCell(8).setCellValue(ep.secondPhase.getAppliedRules());
	    totalTwoRow.createCell(9).setCellValue(ep.secondPhase.getAutomodeTime());
	    Row lastRow = total.createRow(rowcounter+countProjects+3);
	    lastRow.createCell(1).setCellValue(crHelper.createRichTextString("In Total"));
	    ProofStatistics reuse = new ProofStatistics();
	    reuse.addStatistics(ep.firstPhaseReuse);
	    reuse.addStatistics(ep.secondPhaseReuse);
	    ProofStatistics stat = new ProofStatistics();
	    stat.addStatistics(ep.firstPhase);
	    stat.addStatistics(ep.secondPhase);
	    lastRow.createCell(2).setCellValue(reuse.getNodes());
	    lastRow.createCell(3).setCellValue(reuse.getBranches());
	    lastRow.createCell(4).setCellValue(reuse.getAppliedRules());
	    lastRow.createCell(5).setCellValue(reuse.getAutomodeTime());
	    lastRow.createCell(6).setCellValue(stat.getNodes());
	    lastRow.createCell(7).setCellValue(stat.getBranches());
	    lastRow.createCell(8).setCellValue(stat.getAppliedRules());
	    lastRow.createCell(9).setCellValue(stat.getAutomodeTime());
	    lastRow.createCell(10).setCellValue(crHelper.createRichTextString((ep.proofs-ep.failedProofs)+"\\"+ep.proofs));
	    autosizeColumns(total,10);
	    try {
	    	FileOutputStream fOut = new FileOutputStream(ep.statistics);
			wb.write(fOut);
			fOut.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	    try {
			wb.close();
		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}
	
	private static void createMethodSheet(Workbook wb, CreationHelper crHelper,List<ProofStats> ep){
		Sheet s = wb.createSheet(WorkbookUtil.createSafeSheetName("Method Proof Statistics"));
		createColumnTitles(s,crHelper);
		int rowcounter = 1;
		for(ProofStats e: ep){
	    	Row approachRows = s.createRow(rowcounter);
	    	approachRows.createCell(1).setCellValue(crHelper.createRichTextString(e.getType()));
	    	approachRows.createCell(2).setCellValue(crHelper.createRichTextString(e.getTarget()));
	    	approachRows.createCell(3).setCellValue(e.getReusedSum().getNodes());
	    	approachRows.createCell(4).setCellValue(e.getReusedSum().getBranches());
	    	approachRows.createCell(5).setCellValue(e.getReusedSum().getAppliedRules());
	    	approachRows.createCell(6).setCellValue(e.getReusedSum().getAutomodeTime());
	    	approachRows.createCell(7).setCellValue(e.getSum().getNodes());
	    	approachRows.createCell(8).setCellValue(e.getSum().getBranches());
	    	approachRows.createCell(9).setCellValue(e.getSum().getAppliedRules());
	    	approachRows.createCell(10).setCellValue(e.getSum().getAutomodeTime());
	    	approachRows.createCell(11).setCellValue(e.isClosed()? "Yes":"No");
	    	rowcounter++;
	    }
		autosizeColumns(s,12);
	}
	
	/**
	 * Used to read the results of a single project,
	 * because the evaluation is executed in an own jvm
	 * @param s
	 */
	public static void updateSingleProjectsWithReuse(SingleApproachEvaluation s){
		try{
			FileInputStream fis = new FileInputStream(s.statistics);			
		    XSSFWorkbook xssfworkbook = new XSSFWorkbook(fis);
		    XSSFSheet sheet = xssfworkbook.getSheetAt(1);
		    int lastRowNo = sheet.getLastRowNum();
		    XSSFRow currentRow;
		    if(xssfworkbook.getSheetAt(2)!=null){
			    for(int i = 1; i<lastRowNo; i++){
			    	currentRow = sheet.getRow(i);
			    	String type = currentRow.getCell(1).getStringCellValue();
			    	String target = currentRow.getCell(2).getStringCellValue();
			    	int nodes = (int)(currentRow.getCell(7).getNumericCellValue());
			    	int branches = (int)(currentRow.getCell(8).getNumericCellValue());
			    	int appliedRules = (int)(currentRow.getCell(9).getNumericCellValue());
			    	long time = (long)(currentRow.getCell(10).getNumericCellValue());
			    	int reusedNodes = (int)(currentRow.getCell(3).getNumericCellValue());
			    	int reusedBranches = (int)(currentRow.getCell(4).getNumericCellValue());
			    	int reusedAppliedRules = (int)(currentRow.getCell(5).getNumericCellValue());
			    	long reusedTime = (long)(currentRow.getCell(6).getNumericCellValue());
			    	ProofInformation a = new ProofInformation(type,target,"",new ProofStatistics(nodes,branches,appliedRules,time),new ProofStatistics(reusedNodes,reusedBranches,reusedAppliedRules,reusedTime),false);
			    	s.getPhase1ProofList().add(a);
			    }
			    sheet = xssfworkbook.getSheetAt(2);
			    lastRowNo = sheet.getLastRowNum();
		    }
		    for(int i = 1; i<lastRowNo; i++){
		    	currentRow = sheet.getRow(i);
		    	String type = currentRow.getCell(1).getStringCellValue();
		    	String target = currentRow.getCell(2).getStringCellValue();
		    	int nodes = (int)(currentRow.getCell(7).getNumericCellValue());
		    	int branches = (int)(currentRow.getCell(8).getNumericCellValue());
		    	int appliedRules = (int)(currentRow.getCell(9).getNumericCellValue());
		    	long time = (long)(currentRow.getCell(10).getNumericCellValue());
		    	int reusedNodes = (int)(currentRow.getCell(3).getNumericCellValue());
		    	int reusedBranches = (int)(currentRow.getCell(4).getNumericCellValue());
		    	int reusedAppliedRules = (int)(currentRow.getCell(5).getNumericCellValue());
		    	long reusedTime = (long)(currentRow.getCell(6).getNumericCellValue());
		    	String closedValue = currentRow.getCell(11).getStringCellValue();
		    	boolean closed;
		    	if(closedValue.equals("Yes")){
		    		closed = true;
		    	}
		    	else{
		    		closed = false;
		    	}
		    	ProofInformation a = new ProofInformation(type,target,"",new ProofStatistics(nodes,branches,appliedRules,time),new ProofStatistics(reusedNodes,reusedBranches,reusedAppliedRules,reusedTime),closed);
		    	s.getProofList().add(a);
		    }
		    s.updateSum();
		    s.updateFailedProofs();
		    s.updateProofCount();
		    
		    xssfworkbook.close();
		} catch(Exception e){
			e.printStackTrace();
		}
		 
	}
	
	/**
	 * Generates a evaluation summary for a single project
	 * @param s
	 */
	public static void generateSingleProjectWithReuseXLS(SingleApproachEvaluation s){
		Workbook wb = new XSSFWorkbook();
		CreationHelper crHelper = wb.getCreationHelper();
		int rowcount = 0;
		String name = "Total";
		if(s.getPhase1ProofList()!=null){
		    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
		    Row firstRow = total.createRow(0);
		    firstRow.createCell(3).setCellValue(crHelper.createRichTextString("Reused Proof Steps"));
	    	firstRow.createCell(4).setCellValue(crHelper.createRichTextString("Reused Branches"));
	    	firstRow.createCell(5).setCellValue(crHelper.createRichTextString("Reused Applied Rules"));
	    	firstRow.createCell(6).setCellValue(crHelper.createRichTextString("Reused Proof Time"));
	    	firstRow.createCell(7).setCellValue(crHelper.createRichTextString("Proof Steps"));
	    	firstRow.createCell(8).setCellValue(crHelper.createRichTextString("Branches"));
	    	firstRow.createCell(9).setCellValue(crHelper.createRichTextString("Applied Rules"));
	    	firstRow.createCell(10).setCellValue(crHelper.createRichTextString("Proof Time"));
	    	firstRow.createCell(11).setCellValue(crHelper.createRichTextString("Closed Proofs"));
		    ProofStatistics reuseSum = new ProofStatistics();
		    reuseSum.addStatistics(s.firstPhaseReuse);
		    reuseSum.addStatistics(s.secondPhaseReuse);
		    ProofStatistics sum = new ProofStatistics();
		    sum.addStatistics(s.firstPhase);
		    sum.addStatistics(s.secondPhase);
		    createLastRowSingleProject(reuseSum,sum,total,crHelper,1,s);
		    autosizeColumns(total,11);
		    Sheet phaseOne = wb.createSheet(WorkbookUtil.createSafeSheetName("First Phase"));
		    createColumnTitles(phaseOne,crHelper);
		    rowcount = createProofLists(s.getPhase1ProofList(),phaseOne,crHelper,1);
		    createLastRowSingleProject(s.firstPhaseReuse,s.firstPhase,phaseOne,crHelper,rowcount,s);
		    autosizeColumns(phaseOne,10);
		    name = "Second Phase";
	    }
	    Sheet phaseTwo = wb.createSheet(WorkbookUtil.createSafeSheetName(name));
	    createColumnTitles(phaseTwo,crHelper);
	    rowcount = createProofLists(s.getProofList(),phaseTwo,crHelper,1);
	    createLastRowSingleProject(s.secondPhaseReuse,s.secondPhase,phaseTwo,crHelper,rowcount,s);
	    autosizeColumns(phaseTwo,11);
	    Sheet sumOneTwo = wb.createSheet(WorkbookUtil.createSafeSheetName("Sum of Phases"));
	    createColumnTitles(sumOneTwo,crHelper);
	    rowcount = createProofListsForTotalSum(s.getProofList1And2Phase(),sumOneTwo,crHelper,1);
	    autosizeColumns(sumOneTwo,11);
	    try {
	    	FileOutputStream fOut = new FileOutputStream(s.statistics);
			wb.write(fOut);
			fOut.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	    try {
			wb.close();
		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}
	
	private static void createColumnTitles(Sheet s,CreationHelper crHelper){
		Row firstRow = s.createRow(0); 
	    firstRow.createCell(1).setCellValue(crHelper.createRichTextString("Class"));
    	firstRow.createCell(2).setCellValue(crHelper.createRichTextString("Method"));
    	firstRow.createCell(3).setCellValue(crHelper.createRichTextString("Reused Proof Steps"));
    	firstRow.createCell(4).setCellValue(crHelper.createRichTextString("Reused Branches"));
    	firstRow.createCell(5).setCellValue(crHelper.createRichTextString("Reused Applied Rules"));
    	firstRow.createCell(6).setCellValue(crHelper.createRichTextString("Reused Proof Time"));
    	firstRow.createCell(7).setCellValue(crHelper.createRichTextString("Proof Steps"));
    	firstRow.createCell(8).setCellValue(crHelper.createRichTextString("Branches"));
    	firstRow.createCell(9).setCellValue(crHelper.createRichTextString("Applied Rules"));
    	firstRow.createCell(10).setCellValue(crHelper.createRichTextString("Proof Time"));
    	firstRow.createCell(11).setCellValue(crHelper.createRichTextString("Proof Closed"));
	}
	
	private static int createProofLists(List<ProofInformation> ap, Sheet s, CreationHelper crHelper,int start){
		int rowcounter = start;
		for(ProofInformation a: ap){
	    	Row approachRows = s.createRow(rowcounter);
	    	approachRows.createCell(1).setCellValue(crHelper.createRichTextString(a.getTypeName()));
	    	approachRows.createCell(2).setCellValue(crHelper.createRichTextString(a.getTargetName()));
	    	approachRows.createCell(3).setCellValue(a.getReusedStat().getNodes());
	    	approachRows.createCell(4).setCellValue(a.getReusedStat().getBranches());
	    	approachRows.createCell(5).setCellValue(a.getReusedStat().getAppliedRules());
	    	approachRows.createCell(6).setCellValue(a.getReusedStat().getAutomodeTime());
	    	approachRows.createCell(7).setCellValue(a.getStat().getNodes()-a.getReusedStat().getNodes());
	    	approachRows.createCell(8).setCellValue(a.getStat().getBranches()-a.getReusedStat().getBranches());
	    	approachRows.createCell(9).setCellValue(a.getStat().getAppliedRules()-a.getReusedStat().getAppliedRules());
	    	approachRows.createCell(10).setCellValue(a.getStat().getAutomodeTime()-a.getReusedStat().getAutomodeTime());
	    	approachRows.createCell(11).setCellValue(a.isClosed()? "Yes":"No");
	    	rowcounter++;
	    }
		return rowcounter;
	}
	
	private static int createProofListsForTotalSum(List<ProofInformation> ap, Sheet s, CreationHelper crHelper,int start){
		int rowcounter = start;
		for(ProofInformation a: ap){
	    	Row approachRows = s.createRow(rowcounter);
	    	approachRows.createCell(1).setCellValue(crHelper.createRichTextString(a.getTypeName()));
	    	approachRows.createCell(2).setCellValue(crHelper.createRichTextString(a.getTargetName()));
	    	approachRows.createCell(3).setCellValue(a.getReusedStat().getNodes());
	    	approachRows.createCell(4).setCellValue(a.getReusedStat().getBranches());
	    	approachRows.createCell(5).setCellValue(a.getReusedStat().getAppliedRules());
	    	approachRows.createCell(6).setCellValue(a.getReusedStat().getAutomodeTime());
	    	approachRows.createCell(7).setCellValue(a.getStat().getNodes());
	    	approachRows.createCell(8).setCellValue(a.getStat().getBranches());
	    	approachRows.createCell(9).setCellValue(a.getStat().getAppliedRules());
	    	approachRows.createCell(10).setCellValue(a.getStat().getAutomodeTime());
	    	approachRows.createCell(11).setCellValue(a.isClosed()? "Yes":"No");
	    	rowcounter++;
	    }
		return rowcounter;
	}
	
	private static int createProofListsForApproach(List<ProofInformation> ap, Sheet s, CreationHelper crHelper,int start){
		int rowcounter = start;
		for(ProofInformation a: ap){
	    	Row approachRows = s.createRow(rowcounter);
	    	approachRows.createCell(1).setCellValue(crHelper.createRichTextString(a.getTypeName()));
	    	approachRows.createCell(2).setCellValue(crHelper.createRichTextString(a.getTargetName()));
	    	approachRows.createCell(3).setCellValue(a.getReusedStat().getNodes());
	    	approachRows.createCell(4).setCellValue(a.getReusedStat().getBranches());
	    	approachRows.createCell(5).setCellValue(a.getReusedStat().getAppliedRules());
	    	approachRows.createCell(6).setCellValue(a.getReusedStat().getAutomodeTime());
	    	approachRows.createCell(7).setCellValue(a.getStat().getNodes());
	    	approachRows.createCell(8).setCellValue(a.getStat().getBranches());
	    	approachRows.createCell(9).setCellValue(a.getStat().getAppliedRules());
	    	approachRows.createCell(10).setCellValue(a.getStat().getAutomodeTime());
	    	approachRows.createCell(11).setCellValue(a.isClosed()? "Yes":"No");
	    	rowcounter++;
	    }
		return rowcounter;
	}
	
	private static void createLastRowSingleProject(ProofStatistics reused,ProofStatistics stat, Sheet s, CreationHelper crHelper, int rowcounter,SingleApproachEvaluation sp){
		Row lastRow = s.createRow(rowcounter);
	    lastRow.createCell(0).setCellValue(crHelper.createRichTextString("Total"));
    	lastRow.createCell(3).setCellValue(reused.getNodes());
    	lastRow.createCell(4).setCellValue(reused.getBranches());
    	lastRow.createCell(5).setCellValue(reused.getAppliedRules());
    	lastRow.createCell(6).setCellValue(reused.getAutomodeTime());
    	lastRow.createCell(7).setCellValue(stat.getNodes()-reused.getNodes());
    	lastRow.createCell(8).setCellValue(stat.getBranches()-reused.getBranches());
    	lastRow.createCell(9).setCellValue(stat.getAppliedRules()-reused.getAppliedRules());
    	lastRow.createCell(10).setCellValue(stat.getAutomodeTime()-reused.getAutomodeTime());
    	if(s.getSheetName().equals("Total")||s.getSheetName().equals("Second Phase")){
    		lastRow.createCell(11).setCellValue(crHelper.createRichTextString((sp.proofs-sp.failedProofs)+"\\"+sp.proofs));
    	}
	}
	
	private static void createLastRowForApproach(ProofStatistics reused,ProofStatistics stat, Sheet s, CreationHelper crHelper, int rowcounter,String rowName,SingleApproachEvaluation sp){
		Row lastRow = s.createRow(rowcounter);
	    lastRow.createCell(0).setCellValue(crHelper.createRichTextString(rowName));
    	lastRow.createCell(3).setCellValue(reused.getNodes());
    	lastRow.createCell(4).setCellValue(reused.getBranches());
    	lastRow.createCell(5).setCellValue(reused.getAppliedRules());
    	lastRow.createCell(6).setCellValue(reused.getAutomodeTime());
    	lastRow.createCell(7).setCellValue(stat.getNodes());
    	lastRow.createCell(8).setCellValue(stat.getBranches());
    	lastRow.createCell(9).setCellValue(stat.getAppliedRules());
    	lastRow.createCell(10).setCellValue(stat.getAutomodeTime());
    	if(rowName.equals("Total")){
    	lastRow.createCell(11).setCellValue(crHelper.createRichTextString((sp.proofs-sp.failedProofs)+"\\"+sp.proofs));
    	}
	}
	
	private static void autosizeColumns(Sheet s, int columnCount){
		for(int i =0; i<=columnCount;i++){
			s.autoSizeColumn(i);
		}
	}
}
