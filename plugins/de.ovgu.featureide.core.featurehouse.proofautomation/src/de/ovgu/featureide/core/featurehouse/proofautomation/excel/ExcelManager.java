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

import org.apache.poi.hssf.usermodel.HSSFRow;
import org.apache.poi.hssf.usermodel.HSSFSheet;
import org.apache.poi.hssf.usermodel.HSSFWorkbook;
import org.apache.poi.poifs.filesystem.POIFSFileSystem;
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
 * TODO description
 * 
 * @author Stefanie
 */
public class ExcelManager {
	
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
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	    try {
			wb.close();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
	}
	
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
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	    try {
			wb.close();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
	}
	
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
		    XSSFRow lastRow = sheet.getRow(lastRowNo);
/*		    s.setNodeSum((int)(lastRow.getCell(3).getNumericCellValue()));
		    s.setBranchesSum((int)(lastRow.getCell(4).getNumericCellValue()));
		    s.setAppliedRulesSum((int)(lastRow.getCell(5).getNumericCellValue()));
		    s.setAutomodeTimeSum((int)(lastRow.getCell(6).getNumericCellValue()));*/
		    xssfworkbook.close();
		} catch(Exception e){
			e.printStackTrace();
		}
		 
	}
	
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
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	    try {
			wb.close();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
	}
}
