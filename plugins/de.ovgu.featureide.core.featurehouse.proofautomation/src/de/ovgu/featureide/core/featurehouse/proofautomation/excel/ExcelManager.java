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

import org.apache.poi.ss.usermodel.*;
import org.apache.poi.ss.util.WorkbookUtil;
import org.apache.poi.xssf.usermodel.XSSFRow;
import org.apache.poi.xssf.usermodel.XSSFSheet;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;

import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProof;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.CompleteEvaluation;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.EvaluationApproach;
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
	public static void generateAllApproachEvaluationXLS(CompleteEvaluation c){
		Workbook wb = new XSSFWorkbook();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    CreationHelper crHelper = wb.getCreationHelper();
	    Row firstRow = total.createRow(0);
	    firstRow.createCell(0).setCellValue(crHelper.createRichTextString("Evolution"));
	    Row secondRow = total.createRow(1);
	    secondRow.createCell(1).setCellValue(crHelper.createRichTextString("Approach"));
	    secondRow.createCell(2).setCellValue(crHelper.createRichTextString("Proof Steps"));
	    secondRow.createCell(3).setCellValue(crHelper.createRichTextString("Branches"));
	    secondRow.createCell(4).setCellValue(crHelper.createRichTextString("Applied Rules"));
	    secondRow.createCell(5).setCellValue(crHelper.createRichTextString("Proof Time"));
	    int rowcounter = 2;
	    for(EvaluationApproach e: c.getAllApproaches()){
	    	Row approachRow = total.createRow(rowcounter);
	    	approachRow.createCell(1).setCellValue(crHelper.createRichTextString(e.toEvaluate.getName()));
	    	approachRow.createCell(2).setCellValue(e.nodeSum);
	    	approachRow.createCell(3).setCellValue(e.branchesSum);
	    	approachRow.createCell(4).setCellValue(e.appliedRulesSum);
	    	approachRow.createCell(5).setCellValue(e.automodeTimeSum);
	    	rowcounter++;
	    }
	    total.autoSizeColumn(0);
	    total.autoSizeColumn(1);
	    total.autoSizeColumn(2);
	    total.autoSizeColumn(3);
	    total.autoSizeColumn(4);
	    total.autoSizeColumn(5);
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
	
	/**
	 * Generates a summary of all approaches in an xlsx file
	 * @param c
	 */
	public static void generateAllApproachEvaluationWithReuseXLS(CompleteEvaluation c){
		Workbook wb = new XSSFWorkbook();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    CreationHelper crHelper = wb.getCreationHelper();
	    Row firstRow = total.createRow(0);
	    firstRow.createCell(0).setCellValue(crHelper.createRichTextString("Evolution"));
	    Row secondRow = total.createRow(1);
	    secondRow.createCell(1).setCellValue(crHelper.createRichTextString("Approach"));
	    secondRow.createCell(2).setCellValue(crHelper.createRichTextString("Reused Proof Steps"));
	    secondRow.createCell(3).setCellValue(crHelper.createRichTextString("Reused Branches"));
	    secondRow.createCell(4).setCellValue(crHelper.createRichTextString("Reused Applied Rules"));
	    secondRow.createCell(5).setCellValue(crHelper.createRichTextString("ReusedProof Time"));
	    secondRow.createCell(6).setCellValue(crHelper.createRichTextString("Proof Steps"));
	    secondRow.createCell(7).setCellValue(crHelper.createRichTextString("Branches"));
	    secondRow.createCell(8).setCellValue(crHelper.createRichTextString("Applied Rules"));
	    secondRow.createCell(9).setCellValue(crHelper.createRichTextString("Proof Time"));
	    int rowcounter = 2;
	    for(EvaluationApproach e: c.getAllApproaches()){
	    	Row approachRow = total.createRow(rowcounter);
	    	approachRow.createCell(1).setCellValue(crHelper.createRichTextString(e.toEvaluate.getName()));
	    	approachRow.createCell(2).setCellValue(e.reusedNodeSum);
	    	approachRow.createCell(3).setCellValue(e.reusedBranchesSum);
	    	approachRow.createCell(4).setCellValue(e.reusedAppliedRulesSum);
	    	approachRow.createCell(5).setCellValue(e.reusedAutomodeTimeSum);
	    	approachRow.createCell(6).setCellValue(e.nodeSum);
	    	approachRow.createCell(7).setCellValue(e.branchesSum);
	    	approachRow.createCell(8).setCellValue(e.appliedRulesSum);
	    	approachRow.createCell(9).setCellValue(e.automodeTimeSum);
	    	rowcounter++;
	    }
	    total.autoSizeColumn(0);
	    total.autoSizeColumn(1);
	    total.autoSizeColumn(2);
	    total.autoSizeColumn(3);
	    total.autoSizeColumn(4);
	    total.autoSizeColumn(5);
	    total.autoSizeColumn(6);
	    total.autoSizeColumn(7);
	    total.autoSizeColumn(8);
	    total.autoSizeColumn(9);
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
	
	/**
	 * Generates a summary for a single approach in a xlsx file
	 * @param ep
	 */
	public static void generateSingleApproachEvaluationXLS(EvaluationApproach ep){
		Workbook wb = new XSSFWorkbook();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    CreationHelper crHelper = wb.getCreationHelper();
	    Row firstRow = total.createRow(0);
	    firstRow.createCell(0).setCellValue(crHelper.createRichTextString("Evolution"));
	    firstRow.createCell(2).setCellValue(crHelper.createRichTextString("Proof Steps"));
	    firstRow.createCell(3).setCellValue(crHelper.createRichTextString("Branches"));
	    firstRow.createCell(4).setCellValue(crHelper.createRichTextString("Applied Rules"));
	    firstRow.createCell(5).setCellValue(crHelper.createRichTextString("Proof Time"));
	    int rowcounter = 1;
	    for(SingleProject s: ep.getProjectVersion()){
	    	Sheet currentProject = wb.createSheet(WorkbookUtil.createSafeSheetName(s.toEvaluate.getName()));
	    	Row appraochfirstRow = currentProject.createRow(0);
	    	appraochfirstRow.createCell(0).setCellValue(crHelper.createRichTextString("Class"));
	    	appraochfirstRow.createCell(1).setCellValue(crHelper.createRichTextString("Method"));
	    	appraochfirstRow.createCell(2).setCellValue(crHelper.createRichTextString("Proof Steps"));
	    	appraochfirstRow.createCell(3).setCellValue(crHelper.createRichTextString("Branches"));
	    	appraochfirstRow.createCell(4).setCellValue(crHelper.createRichTextString("Applied Rules"));
	    	appraochfirstRow.createCell(5).setCellValue(crHelper.createRichTextString("Proof Time"));
	    	int approachRowCount = 1;
		    for(AutomatingProof a: s.getProofList()){
		    	Row appraochRows = currentProject.createRow(approachRowCount);
		    	appraochRows.createCell(0).setCellValue(crHelper.createRichTextString(a.getTypeName()));
		    	appraochRows.createCell(1).setCellValue(crHelper.createRichTextString(a.getTargetName()));
		    	appraochRows.createCell(2).setCellValue(a.getNodes());
		    	appraochRows.createCell(3).setCellValue(a.getBranches());
		    	appraochRows.createCell(4).setCellValue(a.getAppliedRules());
		    	appraochRows.createCell(5).setCellValue(a.getTime());
		    	approachRowCount++;
		    }
		    Row totalRow = currentProject.createRow(approachRowCount);
		    totalRow.createCell(0).setCellValue("Total");
		    totalRow.createCell(2).setCellValue(s.nodeSum);
		    totalRow.createCell(3).setCellValue(s.branchesSum);
		    totalRow.createCell(4).setCellValue(s.appliedRulesSum);
		    totalRow.createCell(5).setCellValue(s.automodeTimeSum);
		    currentProject.autoSizeColumn(0);
		    currentProject.autoSizeColumn(1);
		    currentProject.autoSizeColumn(2);
		    currentProject.autoSizeColumn(3);
		    currentProject.autoSizeColumn(4);
		    currentProject.autoSizeColumn(5);
	    	Row appraochRow = total.createRow(rowcounter);
	    	appraochRow.createCell(1).setCellValue(crHelper.createRichTextString(s.toEvaluate.getName()));
	    	appraochRow.createCell(2).setCellValue(s.nodeSum);
	    	appraochRow.createCell(3).setCellValue(s.branchesSum);
	    	appraochRow.createCell(4).setCellValue(s.appliedRulesSum);
	    	appraochRow.createCell(5).setCellValue(s.automodeTimeSum);
	    	rowcounter++;
	    }
	    Row lastRow = total.createRow(rowcounter);
	    lastRow.createCell(1).setCellValue(crHelper.createRichTextString("In Total"));
	    lastRow.createCell(2).setCellValue(ep.nodeSum);
	    lastRow.createCell(3).setCellValue(ep.branchesSum);
	    lastRow.createCell(4).setCellValue(ep.appliedRulesSum);
	    lastRow.createCell(5).setCellValue(ep.automodeTimeSum);
	    total.autoSizeColumn(0);
	    total.autoSizeColumn(1);
	    total.autoSizeColumn(2);
	    total.autoSizeColumn(3);
	    total.autoSizeColumn(4);
	    total.autoSizeColumn(5);
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
	 * Generates a summary for a single approach in a xlsx file
	 * @param ep
	 */
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
	    	Row approachfirstRow = currentProject.createRow(0);
	    	approachfirstRow.createCell(0).setCellValue(crHelper.createRichTextString("Class"));
	    	approachfirstRow.createCell(1).setCellValue(crHelper.createRichTextString("Method"));
	    	approachfirstRow.createCell(2).setCellValue(crHelper.createRichTextString("Reused Proof Steps"));
	    	approachfirstRow.createCell(3).setCellValue(crHelper.createRichTextString("Reused Branches"));
	    	approachfirstRow.createCell(4).setCellValue(crHelper.createRichTextString("Reused Applied Rules"));
	    	approachfirstRow.createCell(5).setCellValue(crHelper.createRichTextString("Reused Proof Time"));
	    	approachfirstRow.createCell(6).setCellValue(crHelper.createRichTextString("Proof Steps"));
	    	approachfirstRow.createCell(7).setCellValue(crHelper.createRichTextString("Branches"));
	    	approachfirstRow.createCell(8).setCellValue(crHelper.createRichTextString("Applied Rules"));
	    	approachfirstRow.createCell(9).setCellValue(crHelper.createRichTextString("Proof Time"));
	    	int approachRowCount = 1;
		    for(AutomatingProof a: s.getProofList()){
		    	Row approachRows = currentProject.createRow(approachRowCount);
		    	approachRows.createCell(0).setCellValue(crHelper.createRichTextString(a.getTypeName()));
		    	approachRows.createCell(1).setCellValue(crHelper.createRichTextString(a.getTargetName()));
		    	approachRows.createCell(2).setCellValue(a.getReusedNodes());
		    	approachRows.createCell(3).setCellValue(a.getReusedBranches());
		    	approachRows.createCell(4).setCellValue(a.getReusedAppliedRules());
		    	approachRows.createCell(5).setCellValue(a.getReusedTime());
		    	approachRows.createCell(6).setCellValue(a.getNodes());
		    	approachRows.createCell(7).setCellValue(a.getBranches());
		    	approachRows.createCell(8).setCellValue(a.getAppliedRules());
		    	approachRows.createCell(9).setCellValue(a.getTime());
		    	approachRowCount++;
		    }
		    Row totalRow = currentProject.createRow(approachRowCount);
		    totalRow.createCell(0).setCellValue("Total");
		    totalRow.createCell(2).setCellValue(s.reusedNodeSum);
		    totalRow.createCell(3).setCellValue(s.reusedBranchesSum);
		    totalRow.createCell(4).setCellValue(s.reusedAppliedRulesSum);
		    totalRow.createCell(5).setCellValue(s.reusedAutomodeTimeSum);
		    totalRow.createCell(6).setCellValue(s.nodeSum-s.reusedNodeSum);
		    totalRow.createCell(7).setCellValue(s.branchesSum-s.reusedBranchesSum);
		    totalRow.createCell(8).setCellValue(s.appliedRulesSum-s.reusedAppliedRulesSum);
		    totalRow.createCell(9).setCellValue(s.automodeTimeSum-s.reusedAutomodeTimeSum);
		    currentProject.autoSizeColumn(0);
		    currentProject.autoSizeColumn(1);
		    currentProject.autoSizeColumn(2);
		    currentProject.autoSizeColumn(3);
		    currentProject.autoSizeColumn(4);
		    currentProject.autoSizeColumn(5);
		    currentProject.autoSizeColumn(6);
		    currentProject.autoSizeColumn(7);
		    currentProject.autoSizeColumn(8);
		    currentProject.autoSizeColumn(9);
	    	Row appraochRow = total.createRow(rowcounter);
	    	appraochRow.createCell(1).setCellValue(crHelper.createRichTextString(s.toEvaluate.getName()));
	    	appraochRow.createCell(2).setCellValue(s.reusedNodeSum);
	    	appraochRow.createCell(3).setCellValue(s.reusedBranchesSum);
	    	appraochRow.createCell(4).setCellValue(s.reusedAppliedRulesSum);
	    	appraochRow.createCell(5).setCellValue(s.reusedAutomodeTimeSum);
	    	appraochRow.createCell(6).setCellValue(s.nodeSum-s.reusedNodeSum);
	    	appraochRow.createCell(7).setCellValue(s.branchesSum-s.reusedBranchesSum);
	    	appraochRow.createCell(8).setCellValue(s.appliedRulesSum-s.reusedAppliedRulesSum);
	    	appraochRow.createCell(9).setCellValue(s.automodeTimeSum-s.reusedAutomodeTimeSum);
	    	rowcounter++;
	    }
	    Row lastRow = total.createRow(rowcounter);
	    lastRow.createCell(1).setCellValue(crHelper.createRichTextString("In Total"));
	    lastRow.createCell(2).setCellValue(ep.reusedNodeSum);
	    lastRow.createCell(3).setCellValue(ep.reusedBranchesSum);
	    lastRow.createCell(4).setCellValue(ep.reusedAppliedRulesSum);
	    lastRow.createCell(5).setCellValue(ep.reusedAutomodeTimeSum);
	    lastRow.createCell(6).setCellValue(ep.nodeSum-ep.reusedNodeSum);
	    lastRow.createCell(7).setCellValue(ep.branchesSum-ep.reusedBranchesSum);
	    lastRow.createCell(8).setCellValue(ep.appliedRulesSum-ep.reusedAppliedRulesSum);
	    lastRow.createCell(9).setCellValue(ep.automodeTimeSum-ep.reusedAutomodeTimeSum);
	    total.autoSizeColumn(0);
	    total.autoSizeColumn(1);
	    total.autoSizeColumn(2);
	    total.autoSizeColumn(3);
	    total.autoSizeColumn(4);
	    total.autoSizeColumn(5);
	    total.autoSizeColumn(6);
	    total.autoSizeColumn(7);
	    total.autoSizeColumn(8);
	    total.autoSizeColumn(9);
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
	public static void updateSingleProjects(SingleProject s){
		try{
			FileInputStream fis = new FileInputStream(s.statistics);
		    XSSFWorkbook xssfworkbook = new XSSFWorkbook(fis);
		    XSSFSheet sheet = xssfworkbook.getSheetAt(0);
		    int lastRowNo = sheet.getLastRowNum();
		    XSSFRow currentRow;
		    for(int i = 1; i<lastRowNo; i++){
		    	currentRow = sheet.getRow(i);
		    	String type = currentRow.getCell(1).getStringCellValue();
		    	String target = currentRow.getCell(2).getStringCellValue();
		    	int nodes = (int)(currentRow.getCell(3).getNumericCellValue());
		    	int branches = (int)(currentRow.getCell(4).getNumericCellValue());
		    	int appliedRules = (int)(currentRow.getCell(5).getNumericCellValue());
		    	long time = (long)(currentRow.getCell(6).getNumericCellValue());
		    	AutomatingProof a = new AutomatingProof(type,target,nodes,branches,appliedRules,time);
		    	s.getProofList().add(a);
		    }
		    s.updateSum();
		    xssfworkbook.close();
		} catch(Exception e){
			e.printStackTrace();
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
		    XSSFSheet sheet = xssfworkbook.getSheetAt(0);
		    int lastRowNo = sheet.getLastRowNum();
		    XSSFRow currentRow;
		    for(int i = 1; i<lastRowNo; i++){
		    	currentRow = sheet.getRow(i);
		    	String type = currentRow.getCell(1).getStringCellValue();
		    	String target = currentRow.getCell(2).getStringCellValue();
		    	int nodes = (int)(currentRow.getCell(7).getNumericCellValue());
		    	int branches = (int)(currentRow.getCell(8).getNumericCellValue());
		    	int appliedRules = (int)(currentRow.getCell(9).getNumericCellValue());
		    	long time = (long)(currentRow.getCell(10).getNumericCellValue());
		    	AutomatingProof a = new AutomatingProof(type,target,nodes,branches,appliedRules,time);
		    	a.setReusedAppliedRules((int)(currentRow.getCell(5).getNumericCellValue()));
		    	a.setReusedBranches((int)(currentRow.getCell(4).getNumericCellValue()));
		    	a.setReusedNodes((int)(currentRow.getCell(3).getNumericCellValue()));
		    	a.setReusedTime((long)(currentRow.getCell(6).getNumericCellValue()));
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
	public static void generateSingleProjectXLS(SingleProject s){
		Workbook wb = new XSSFWorkbook();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    CreationHelper crHelper = wb.getCreationHelper();
	    Row appraochfirstRow = total.createRow(0); 
	    appraochfirstRow.createCell(1).setCellValue(crHelper.createRichTextString("Class"));
    	appraochfirstRow.createCell(2).setCellValue(crHelper.createRichTextString("Method"));
    	appraochfirstRow.createCell(3).setCellValue(crHelper.createRichTextString("Proof Steps"));
    	appraochfirstRow.createCell(4).setCellValue(crHelper.createRichTextString("Branches"));
    	appraochfirstRow.createCell(5).setCellValue(crHelper.createRichTextString("Applied Rules"));
    	appraochfirstRow.createCell(6).setCellValue(crHelper.createRichTextString("Proof Time"));
	    int rowcounter = 1;
	    for(AutomatingProof a: s.getProofList()){
	    	Row approachRows = total.createRow(rowcounter);
	    	approachRows.createCell(1).setCellValue(crHelper.createRichTextString(a.getTypeName()));
	    	approachRows.createCell(2).setCellValue(crHelper.createRichTextString(a.getTargetName()));
	    	approachRows.createCell(3).setCellValue(a.getNodes());
	    	approachRows.createCell(4).setCellValue(a.getBranches());
	    	approachRows.createCell(5).setCellValue(a.getAppliedRules());
	    	approachRows.createCell(6).setCellValue(a.getTime());
	    	rowcounter++;
	    }
	    Row lastRow = total.createRow(rowcounter);
	    lastRow.createCell(0).setCellValue(crHelper.createRichTextString("Total"));
    	lastRow.createCell(3).setCellValue(s.nodeSum);
    	lastRow.createCell(4).setCellValue(s.branchesSum);
    	lastRow.createCell(5).setCellValue(s.appliedRulesSum);
    	lastRow.createCell(6).setCellValue(s.automodeTimeSum);
	    total.autoSizeColumn(0);
	    total.autoSizeColumn(1);
	    total.autoSizeColumn(2);
	    total.autoSizeColumn(3);
	    total.autoSizeColumn(4);
	    total.autoSizeColumn(5);
	    total.autoSizeColumn(6);
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
	
	/**
	 * Generates a evaluation summary for a single project
	 * @param s
	 */
	public static void generateSingleProjectWithReuseXLS(SingleProject s){
		Workbook wb = new XSSFWorkbook();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    CreationHelper crHelper = wb.getCreationHelper();
	    Row appraochfirstRow = total.createRow(0); 
	    appraochfirstRow.createCell(1).setCellValue(crHelper.createRichTextString("Class"));
    	appraochfirstRow.createCell(2).setCellValue(crHelper.createRichTextString("Method"));
    	appraochfirstRow.createCell(3).setCellValue(crHelper.createRichTextString("Reused Proof Steps"));
    	appraochfirstRow.createCell(4).setCellValue(crHelper.createRichTextString("Reused Branches"));
    	appraochfirstRow.createCell(5).setCellValue(crHelper.createRichTextString("Reused Applied Rules"));
    	appraochfirstRow.createCell(6).setCellValue(crHelper.createRichTextString("Reused Proof Time"));
    	appraochfirstRow.createCell(7).setCellValue(crHelper.createRichTextString("Proof Steps"));
    	appraochfirstRow.createCell(8).setCellValue(crHelper.createRichTextString("Branches"));
    	appraochfirstRow.createCell(9).setCellValue(crHelper.createRichTextString("Applied Rules"));
    	appraochfirstRow.createCell(10).setCellValue(crHelper.createRichTextString("Proof Time"));
	    int rowcounter = 1;
	    for(AutomatingProof a: s.getProofList()){
	    	Row approachRows = total.createRow(rowcounter);
	    	approachRows.createCell(1).setCellValue(crHelper.createRichTextString(a.getTypeName()));
	    	approachRows.createCell(2).setCellValue(crHelper.createRichTextString(a.getTargetName()));
	    	approachRows.createCell(3).setCellValue(a.getReusedNodes());
	    	approachRows.createCell(4).setCellValue(a.getReusedBranches());
	    	approachRows.createCell(5).setCellValue(a.getReusedAppliedRules());
	    	approachRows.createCell(6).setCellValue(a.getReusedTime());
	    	approachRows.createCell(7).setCellValue(a.getNodes()-a.getReusedNodes());
	    	approachRows.createCell(8).setCellValue(a.getBranches()-a.getReusedBranches());
	    	approachRows.createCell(9).setCellValue(a.getAppliedRules()-a.getReusedAppliedRules());
	    	approachRows.createCell(10).setCellValue(a.getTime()-a.getReusedTime());
	    	rowcounter++;
	    }
	    Row lastRow = total.createRow(rowcounter);
	    lastRow.createCell(0).setCellValue(crHelper.createRichTextString("Total"));
    	lastRow.createCell(3).setCellValue(s.reusedNodeSum);
    	lastRow.createCell(4).setCellValue(s.reusedBranchesSum);
    	lastRow.createCell(5).setCellValue(s.reusedAppliedRulesSum);
    	lastRow.createCell(6).setCellValue(s.reusedAutomodeTimeSum);
    	lastRow.createCell(7).setCellValue(s.nodeSum-s.reusedNodeSum);
    	lastRow.createCell(8).setCellValue(s.branchesSum-s.reusedBranchesSum);
    	lastRow.createCell(9).setCellValue(s.appliedRulesSum-s.reusedAppliedRulesSum);
    	lastRow.createCell(10).setCellValue(s.automodeTimeSum-s.reusedAutomodeTimeSum);
	    total.autoSizeColumn(0);
	    total.autoSizeColumn(1);
	    total.autoSizeColumn(2);
	    total.autoSizeColumn(3);
	    total.autoSizeColumn(4);
	    total.autoSizeColumn(5);
	    total.autoSizeColumn(6);
	    total.autoSizeColumn(7);
	    total.autoSizeColumn(8);
	    total.autoSizeColumn(9);
	    total.autoSizeColumn(10);
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
}
