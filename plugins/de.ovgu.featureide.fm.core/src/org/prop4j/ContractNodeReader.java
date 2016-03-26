/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package org.prop4j;

import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * This class can be used to parse contract clauses into nodes.
 * 
 * @author Sebastian Krieter
 * @author Stefan Krueger
 */
public class ContractNodeReader {

	public final static String[] shortSymbols = new String[] { "<==>", "==>", "||", "&&", "!" };
	private final static String fmPrefix = "FM.FeatureModel.";

	public Node parseStringToNode(String constraint) {
		constraint = constraint.trim();
		if (constraint.isEmpty()) {
			throw new RuntimeException("Clause is empty.");
		}
		return getExpressions(constraint);
	}

	private Node getExpressions(String constraint) {
		constraint = constraint.trim();
		Node curNode = null;
		int op = -1;

		final StringBuilder expressionBuilder = new StringBuilder();
		int bracketCounter = 0;
		for (int i = constraint.length() - 1; i >= 0; i--) {
			char curChar = constraint.charAt(i);
			if (curChar == ')') {
				bracketCounter++;
			} else if (curChar == '(') {
				if (bracketCounter == 0) {
					throw new RuntimeException("Invalid Positioning of Parentheses");
				}
				bracketCounter--;
				if (bracketCounter == 0) {
					if (i == 0 && curNode == null) {
						curNode = getExpressions(expressionBuilder.reverse().substring(0, expressionBuilder.length() - 1));
						expressionBuilder.setLength(0);
						continue;
					}
				}
			} else if (bracketCounter == 0) {
				if (curChar == '!') {
					if (constraint.length() > i + 1 && constraint.charAt(i + 1) != '=') {
						final Not tmpNode = new Not(expressionBuilder.reverse().toString().trim());
						curNode = pickNodeType(curNode, op, tmpNode);
						op = -1;
						expressionBuilder.setLength(0);
						continue;
					}
				} else if (curChar == '&') {
					if (0 <= i - 1 && constraint.charAt(i - 1) == '&') {
						curNode = createNode(curNode, op, expressionBuilder);
						op = 3;
						i--;
						continue;
					}
				} else if (curChar == '|') {
					if (0 <= i - 1 && constraint.charAt(i - 1) == '|') {
						curNode = createNode(curNode, op, expressionBuilder);
						op = 2;
						i--;
						continue;
					}
				} else if (curChar == '>') {
					if (0 <= i - 3 && constraint.charAt(i - 1) == '=' && constraint.charAt(i - 2) == '=' && constraint.charAt(i - 3) == '<') {
						curNode = createNode(curNode, op, expressionBuilder);
						op = 0;
						i -= 3;
						continue;
					}
					if (0 <= i - 2 && constraint.charAt(i - 1) == '=' && constraint.charAt(i - 2) == '=') {
						curNode = createNode(curNode, op, expressionBuilder);
						op = 1;
						i -= 2;
						continue;
					}
				}
			}
			expressionBuilder.append(curChar);
		}

		if (bracketCounter > 0) {
			throw new RuntimeException("invalid number of parentheses: too many '('");
		}

		if (expressionBuilder.length() > 0) {
			if (curNode == null) {
				if (constraint.startsWith(fmPrefix)) {
					return new Literal(constraint.substring(fmPrefix.length()).trim());
				} else if (constraint.equals("true")) {
					return new Literal(NodeCreator.varTrue);
				} else {
					return new ExpressionLiteral(constraint);
				}
			} else {
				curNode = createNode(curNode, op, expressionBuilder);
			}
		}

		return curNode;
	}

	private Node createNode(Node curNode, int op, final StringBuilder expressionBuilder) {
		if (curNode == null || op > -1) {
			final Node tmpNode = getExpressions(expressionBuilder.reverse().toString().trim());
			curNode = pickNodeType(curNode, op, tmpNode);
		}
		expressionBuilder.setLength(0);
		return curNode;
	}

	private Node pickNodeType(Node curNode, int op, final Node tmpNode) {
		switch (op) {
		case 0:
			curNode = new Equals(tmpNode, curNode);
			break;
		case 1:
			curNode = new Implies(tmpNode, curNode);
			break;
		case 2:
			curNode = new Or(tmpNode, curNode);
			break;
		case 3:
			curNode = new And(tmpNode, curNode);
			break;
		default:
			curNode = tmpNode;
		}
		return curNode;
	}
}
