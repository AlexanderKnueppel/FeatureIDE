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

/**
 * Literal Node in case the value of the node needs to be saved
 * 
 * @author Sebastian Krieter
 * @author Stefan Krueger
 */
public class ExpressionLiteral extends Literal {

	private final String expression;

	public ExpressionLiteral(String expression) {
		super(varExp);
		this.expression = expression;
	}

	public String getExpression() {
		return expression;
	}

	@Override
	public Literal clone() {
		ExpressionLiteral clone = new ExpressionLiteral(expression);
		clone.positive = this.positive;
		return clone;
	}

	@Override
	public boolean equals(Object node) {
		return super.equals(node) && (node instanceof ExpressionLiteral) && ((ExpressionLiteral) node).expression.equals(expression);
	}

	public StringBuilder toString(StringBuilder nodeStringBuilder, int level) {
		for (int i = 0; i < level; i++) {
			nodeStringBuilder.append("\t");
		}
		nodeStringBuilder.append("EXP: " + expression);

		return super.toString(nodeStringBuilder, level);
	}
	
	public final static Object varExp = new Object() {
		public String toString() {
			return "Exp";
		};
	};
}
