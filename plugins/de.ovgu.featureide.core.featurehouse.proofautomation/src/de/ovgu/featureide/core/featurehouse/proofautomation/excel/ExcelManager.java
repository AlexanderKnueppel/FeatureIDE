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

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.apache.poi.ss.usermodel.*;
import org.apache.poi.ss.util.WorkbookUtil;
import org.apache.poi.xssf.usermodel.XSSFRow;
import org.apache.poi.xssf.usermodel.XSSFSheet;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;

import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProof;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.CompleteEvaluation;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.EvaluationApproach;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.ProofStatistics;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.SingleProject;

/**
 * Saves the evaluation in excel files 
 * 
 * @author Stefanie
 */
public class ExcelManager {	
	/**
	 * Generates a summary of all approaches in an xlsx file
	 * @param c
	 */
	public static void generateAllApproachEvaluationWithReuseXLS(CompleteEvaluation c){
		Workbook wb = new XSSFWorkbook();
		CreationHelper crHelper = wb.getCreationHelper();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    fullEvaluationTitles(total,crHelper);
	    Sheet phaseOne = wb.createSheet(WorkbookUtil.createSafeSheetName("First Phase"));
	    fullEvaluationTitles(phaseOne,crHelper);
	    Sheet phaseTwo = wb.createSheet(WorkbookUtil.createSafeSheetName("Second Phase"));
	    fullEvaluationTitles(phaseTwo,crHelper);	    
	    int rowcounter = 2;
	    for(EvaluationApproach e: c.getAllApproaches()){
	    	ProofStatistics reuse = new ProofStatistics();
		    reuse.addStatistics(e.firstPhaseReuse);
		    reuse.addStatistics(e.secondPhaseReuse);
		    ProofStatistics stat = new ProofStatistics();
		    stat.addStatistics(e.firstPhase);
		    stat.addStatistics(e.secondPhase);
	    	proofLists(total,crHelper, e.toEvaluate.getName(),reuse,stat, rowcounter);
	    	proofLists(phaseOne,crHelper, e.toEvaluate.getName(),e.firstPhaseReuse,e.firstPhase, rowcounter);
	    	proofLists(phaseTwo,crHelper, e.toEvaluate.getName(),e.secondPhaseReuse,e.secondPhase, rowcounter);
	    	rowcounter++;
	    }
	    autosizeColumns(total,9);
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
	
	private static void proofLists(Sheet s, CreationHelper crHelper, String name, ProofStatistics reuse, ProofStatistics stat, int rowcounter){
		Row approachRow = s.createRow(rowcounter);
    	approachRow.createCell(1).setCellValue(crHelper.createRichTextString(name));
    	approachRow.createCell(2).setCellValue(reuse.getNodes());
    	approachRow.createCell(3).setCellValue(reuse.getBranches());
    	approachRow.createCell(4).setCellValue(reuse.getAppliedRules());
    	approachRow.createCell(5).setCellValue(reuse.getAutomodeTime());
    	approachRow.createCell(6).setCellValue(stat.getNodes());
    	approachRow.createCell(7).setCellValue(stat.getBranches());
    	approachRow.createCell(8).setCellValue(stat.getAppliedRules());
    	approachRow.createCell(9).setCellValue(stat.getAutomodeTime());
	}
	private static void fullEvaluationTitles(Sheet s, CreationHelper crHelper){
		Row firstRow = s.createRow(0);
	    firstRow.createCell(0).setCellValue(crHelper.createRichTextString("Evolution"));
		Row secondRow = s.createRow(1);
	    secondRow.createCell(1).setCellValue(crHelper.createRichTextString("Approach"));
	    secondRow.createCell(2).setCellValue(crHelper.createRichTextString("Reused Proof Steps"));
	    secondRow.createCell(3).setCellValue(crHelper.createRichTextString("Reused Branches"));
	    secondRow.createCell(4).setCellValue(crHelper.createRichTextString("Reused Applied Rules"));
	    secondRow.createCell(5).setCellValue(crHelper.createRichTextString("ReusedProof Time"));
	    secondRow.createCell(6).setCellValue(crHelper.createRichTextString("Proof Steps"));
	    secondRow.createCell(7).setCellValue(crHelper.createRichTextString("Branches"));
	    secondRow.createCell(8).setCellValue(crHelper.createRichTextString("Applied Rules"));
	    secondRow.createCell(9).setCellValue(crHelper.createRichTextString("Proof Time"));
	}
	
	public static void generateSingleApproachEvaluationWithReuseXLS(EvaluationApproach ep){
		Workbook wb = new XSSFWorkbook();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    CreationHelper crHelper = wb.getCreationHelper();
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
	    int rowcounter = 1;
	    for(SingleProject s: ep.getProjectVersion()){
	    	Sheet currentProject = wb.createSheet(WorkbookUtil.createSafeSheetName(s.toEvaluate.getName()));
	    	createColumnTitles(currentProject,crHelper);
	    	int rowcount = 1;
		    rowcount = createProofListsForApproach(s.getProofList(),currentProject,crHelper,rowcount);
		    createLastRowForApproach(s.secondPhaseReuse,s.secondPhase,currentProject,crHelper,rowcount,"Total");
		    autosizeColumns(currentProject,10);
	    }
	    for(SingleProject s : ep.getProjectVersion()){
	    	Row appraochRow = total.createRow(rowcounter);
	    	appraochRow.createCell(1).setCellValue(crHelper.createRichTextString(s.toEvaluate.getName()));
	    	appraochRow.createCell(2).setCellValue(s.secondPhaseReuse.getNodes());
	    	appraochRow.createCell(3).setCellValue(s.secondPhaseReuse.getBranches());
	    	appraochRow.createCell(4).setCellValue(s.secondPhaseReuse.getAppliedRules());
	    	appraochRow.createCell(5).setCellValue(s.secondPhaseReuse.getAutomodeTime());
	    	appraochRow.createCell(6).setCellValue(s.secondPhase.getNodes());
	    	appraochRow.createCell(7).setCellValue(s.secondPhase.getBranches());
	    	appraochRow.createCell(8).setCellValue(s.secondPhase.getAppliedRules());
	    	appraochRow.createCell(9).setCellValue(s.secondPhase.getAutomodeTime());
	    	rowcounter++;
	    }
	    Row totalTwoRow = total.createRow(rowcounter);
	    totalTwoRow.createCell(0).setCellValue(crHelper.createRichTextString("Total"));
	    totalTwoRow.createCell(2).setCellValue(ep.secondPhaseReuse.getNodes());
	    totalTwoRow.createCell(3).setCellValue(ep.secondPhaseReuse.getBranches());
	    totalTwoRow.createCell(4).setCellValue(ep.secondPhaseReuse.getAppliedRules());
	    totalTwoRow.createCell(5).setCellValue(ep.secondPhaseReuse.getAutomodeTime());
	    totalTwoRow.createCell(6).setCellValue(ep.secondPhase.getNodes());
	    totalTwoRow.createCell(7).setCellValue(ep.secondPhase.getBranches());
	    totalTwoRow.createCell(8).setCellValue(ep.secondPhase.getAppliedRules());
	    totalTwoRow.createCell(9).setCellValue(ep.secondPhase.getAutomodeTime());
	    autosizeColumns(total,9);
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
	
	public static void generateSingleApproachTwoPhaseEvaluationWithReuseXLS(EvaluationApproach ep){
		Workbook wb = new XSSFWorkbook();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    CreationHelper crHelper = wb.getCreationHelper();
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
	    Row secondRow = total.createRow(1);
	    secondRow.createCell(0).setCellValue(crHelper.createRichTextString("First Phase"));
	    int rowcounter = 2;
	    int countProjects = 0;
	    for(SingleProject s: ep.getProjectVersion()){
	    	Sheet currentProject = wb.createSheet(WorkbookUtil.createSafeSheetName(s.toEvaluate.getName()));
	    	createColumnTitles(currentProject,crHelper);
	    	int rowcount = 1;
    		Row phaseRow = currentProject.createRow(rowcount);
    		phaseRow.createCell(0).setCellValue(crHelper.createRichTextString("First Phase"));
    		rowcount++;
    		rowcount = createProofListsForApproach(s.getPhase1ProofList(),currentProject,crHelper,rowcount);
    		createLastRowForApproach(s.firstPhaseReuse,s.firstPhase,currentProject,crHelper,rowcount,"First Phase Total");
    		rowcount++;
    		phaseRow = currentProject.createRow(rowcount);
    		phaseRow.createCell(0).setCellValue(crHelper.createRichTextString("Second Phase"));
    		rowcount++;
		    rowcount = createProofListsForApproach(s.getProofList(),currentProject,crHelper,rowcount);
		    createLastRowForApproach(s.secondPhaseReuse,s.secondPhase,currentProject,crHelper,rowcount,"Second Phase Total");
		    rowcount++;
		    ProofStatistics reuseSum = new ProofStatistics();
		    reuseSum.addStatistics(s.firstPhaseReuse);
		    reuseSum.addStatistics(s.secondPhaseReuse);
		    ProofStatistics sum = new ProofStatistics();
		    sum.addStatistics(s.firstPhase);
		    sum.addStatistics(s.secondPhase);
		    createLastRowForApproach(reuseSum,sum,currentProject,crHelper,rowcount,"Total");
		    autosizeColumns(currentProject,10);
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
	    for(SingleProject s : ep.getProjectVersion()){
	    	Row appraochRow = total.createRow(rowcounter);
	    	appraochRow.createCell(1).setCellValue(crHelper.createRichTextString(s.toEvaluate.getName()));
	    	appraochRow.createCell(2).setCellValue(s.firstPhaseReuse.getNodes());
	    	appraochRow.createCell(3).setCellValue(s.firstPhaseReuse.getBranches());
	    	appraochRow.createCell(4).setCellValue(s.firstPhaseReuse.getAppliedRules());
	    	appraochRow.createCell(5).setCellValue(s.firstPhaseReuse.getAutomodeTime());
	    	appraochRow.createCell(6).setCellValue(s.firstPhase.getNodes());
	    	appraochRow.createCell(7).setCellValue(s.firstPhase.getBranches());
	    	appraochRow.createCell(8).setCellValue(s.firstPhase.getAppliedRules());
	    	appraochRow.createCell(9).setCellValue(s.firstPhase.getAutomodeTime());
	    	appraochRow = total.createRow(rowcounter+countProjects+2);
	    	appraochRow.createCell(1).setCellValue(crHelper.createRichTextString(s.toEvaluate.getName()));
	    	appraochRow.createCell(2).setCellValue(s.secondPhaseReuse.getNodes());
	    	appraochRow.createCell(3).setCellValue(s.secondPhaseReuse.getBranches());
	    	appraochRow.createCell(4).setCellValue(s.secondPhaseReuse.getAppliedRules());
	    	appraochRow.createCell(5).setCellValue(s.secondPhaseReuse.getAutomodeTime());
	    	appraochRow.createCell(6).setCellValue(s.secondPhase.getNodes());
	    	appraochRow.createCell(7).setCellValue(s.secondPhase.getBranches());
	    	appraochRow.createCell(8).setCellValue(s.secondPhase.getAppliedRules());
	    	appraochRow.createCell(9).setCellValue(s.secondPhase.getAutomodeTime());
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
	    autosizeColumns(total,9);
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
	
	
	/**
	 * Used to read the results of a single project,
	 * because the evaluation is executed in an own jvm
	 * @param s
	 */
	public static void updateSingleProjectsWithReuse(SingleProject s){
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
			    	AutomatingProof a = new AutomatingProof(type,target,nodes,branches,appliedRules,time,reusedNodes,reusedBranches,reusedAppliedRules,reusedTime);
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
		    	AutomatingProof a = new AutomatingProof(type,target,nodes,branches,appliedRules,time,reusedNodes,reusedBranches,reusedAppliedRules,reusedTime);
		    	s.getProofList().add(a);
		    }
		    s.updateSum();
		    xssfworkbook.close();
		} catch(Exception e){
			e.printStackTrace();
		}
		 
	}
	
	/**
	 * Generates a evaluation summary for a single project
	 * @param s
	 */
	public static void generateSingleProjectWithReuseXLS(SingleProject s){
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
		    ProofStatistics reuseSum = new ProofStatistics();
		    reuseSum.addStatistics(s.firstPhaseReuse);
		    reuseSum.addStatistics(s.secondPhaseReuse);
		    ProofStatistics sum = new ProofStatistics();
		    sum.addStatistics(s.firstPhase);
		    sum.addStatistics(s.secondPhase);
		    createLastRowSingleProject(reuseSum,sum,total,crHelper,1);
		    autosizeColumns(total,10);
		    Sheet phaseOne = wb.createSheet(WorkbookUtil.createSafeSheetName("First Phase"));
		    createColumnTitles(phaseOne,crHelper);
		    rowcount = createProofLists(s.getPhase1ProofList(),phaseOne,crHelper,1);
		    createLastRowSingleProject(s.firstPhaseReuse,s.firstPhase,phaseOne,crHelper,rowcount);
		    autosizeColumns(phaseOne,10);
		    name = "Second Phase";
	    }
	    Sheet phaseTwo = wb.createSheet(WorkbookUtil.createSafeSheetName(name));
	    createColumnTitles(phaseTwo,crHelper);
	    rowcount = createProofLists(s.getProofList(),phaseTwo,crHelper,1);
	    createLastRowSingleProject(s.secondPhaseReuse,s.secondPhase,phaseTwo,crHelper,rowcount);
	    autosizeColumns(phaseTwo,10);
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
	}
	
	private static int createProofLists(List<AutomatingProof> ap, Sheet s, CreationHelper crHelper,int start){
		int rowcounter = start;
		for(AutomatingProof a: ap){
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
	    	rowcounter++;
	    }
		return rowcounter;
	}
	
	private static int createProofListsForApproach(List<AutomatingProof> ap, Sheet s, CreationHelper crHelper,int start){
		int rowcounter = start;
		for(AutomatingProof a: ap){
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
	    	rowcounter++;
	    }
		return rowcounter;
	}
	
	private static void createLastRowSingleProject(ProofStatistics reused,ProofStatistics stat, Sheet s, CreationHelper crHelper, int rowcounter){
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
	}
	
	private static void createLastRowForApproach(ProofStatistics reused,ProofStatistics stat, Sheet s, CreationHelper crHelper, int rowcounter,String rowName){
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
	}
	
	private static void autosizeColumns(Sheet s, int columnCount){
		for(int i =0; i<=columnCount;i++){
			s.autoSizeColumn(i);
		}
	}
}
