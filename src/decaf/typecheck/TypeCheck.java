package decaf.typecheck;

import java.util.Iterator;
import java.util.List;
import java.util.Stack;

import decaf.Driver;
import decaf.Location;
import decaf.tree.Tree;
import decaf.error.*;
import decaf.frontend.Parser;
import decaf.scope.ClassScope;
import decaf.scope.FormalScope;
import decaf.scope.Scope;
import decaf.scope.ScopeStack;
import decaf.scope.LocalScope;
import decaf.scope.Scope.Kind;
import decaf.symbol.Class;
import decaf.symbol.Function;
import decaf.symbol.Symbol;
import decaf.symbol.Variable;
import decaf.type.*;

public class TypeCheck extends Tree.Visitor {

	private ScopeStack table;

	private Stack<Tree> breaks;

	private Function currentFunction;

	public TypeCheck(ScopeStack table) {
		this.table = table;
		breaks = new Stack<Tree>();
	}

	public static void checkType(Tree.TopLevel tree) {
		new TypeCheck(Driver.getDriver().getTable()).visitTopLevel(tree);
	}

	@Override
	public void visitBinary(Tree.Binary expr) {
		expr.type = checkBinaryOp(expr.left, expr.right, expr.tag, expr.loc);
	}

	@Override
	public void visitUnary(Tree.Unary expr) {
		expr.expr.accept(this);
		if(expr.tag == Tree.NEG){
			if (expr.expr.type.equal(BaseType.ERROR)
					|| expr.expr.type.equal(BaseType.INT)) {
				expr.type = expr.expr.type;
			} else {
				issueError(new IncompatUnOpError(expr.getLocation(), "-",
						expr.expr.type.toString()));
				expr.type = BaseType.ERROR;
			}
		}
		else{
			if (!(expr.expr.type.equal(BaseType.BOOL) || expr.expr.type
					.equal(BaseType.ERROR))) {
				issueError(new IncompatUnOpError(expr.getLocation(), "!",
						expr.expr.type.toString()));
			}
			expr.type = BaseType.BOOL;
		}
	}

	@Override
	public void visitLiteral(Tree.Literal literal) {
		switch (literal.typeTag) {
		case Tree.INT:
			literal.type = BaseType.INT;
			break;
		case Tree.BOOL:
			literal.type = BaseType.BOOL;
			break;
		case Tree.STRING:
			literal.type = BaseType.STRING;
			break;
		}
	}

	@Override
	public void visitNull(Tree.Null nullExpr) {
		nullExpr.type = BaseType.NULL;
	}

	@Override
	public void visitReadIntExpr(Tree.ReadIntExpr readIntExpr) {
		readIntExpr.type = BaseType.INT;
	}

	@Override
	public void visitReadLineExpr(Tree.ReadLineExpr readStringExpr) {
		readStringExpr.type = BaseType.STRING;
	}

	@Override
	public void visitIndexed(Tree.Indexed indexed) {
		indexed.lvKind = Tree.LValue.Kind.ARRAY_ELEMENT;
		indexed.array.accept(this);
		if (!indexed.array.type.isArrayType()) {
			issueError(new NotArrayError(indexed.array.getLocation()));
			indexed.type = BaseType.ERROR;
		} else {
			indexed.type = ((ArrayType) indexed.array.type)
					.getElementType();
		}
		indexed.index.accept(this);
		if (!indexed.index.type.equal(BaseType.INT)) {
			issueError(new SubNotIntError(indexed.getLocation()));
		}
	}

	private void checkCallExpr(Tree.CallExpr callExpr, Symbol f) {
		Type receiverType = callExpr.receiver == null ? ((ClassScope) table
				.lookForScope(Scope.Kind.CLASS)).getOwner().getType()
				: callExpr.receiver.type;
		if (f == null) {
			issueError(new FieldNotFoundError(callExpr.getLocation(),
					callExpr.method, receiverType.toString()));
			callExpr.type = BaseType.ERROR;
		} else if (!f.isFunction()) {
			issueError(new NotClassMethodError(callExpr.getLocation(),
					callExpr.method, receiverType.toString()));
			callExpr.type = BaseType.ERROR;
		} else {
			Function func = (Function) f;
			callExpr.symbol = func;
			callExpr.type = func.getReturnType();
			if (callExpr.receiver == null && currentFunction.isStatik()
					&& !func.isStatik()) {
				issueError(new RefNonStaticError(callExpr.getLocation(),
						currentFunction.getName(), func.getName()));
			}
			if (!func.isStatik() && callExpr.receiver != null
					&& callExpr.receiver.isClass) {
				issueError(new NotClassFieldError(callExpr.getLocation(),
						callExpr.method, callExpr.receiver.type.toString()));
			}
			if (func.isStatik()) {
				callExpr.receiver = null;
			} else {
				if (callExpr.receiver == null && !currentFunction.isStatik()) {
					callExpr.receiver = new Tree.ThisExpr(callExpr.getLocation());
					callExpr.receiver.accept(this);
				}
			}
			for (Tree.Expr e : callExpr.actuals) {
				e.accept(this);
			}
			List<Type> argList = func.getType().getArgList();
			int argCount = func.isStatik() ? callExpr.actuals.size()
					: callExpr.actuals.size() + 1;
			if (argList.size() != argCount) {
				issueError(new BadArgCountError(callExpr.getLocation(),
						callExpr.method, func.isStatik() ? argList.size()
								: argList.size() - 1, callExpr.actuals.size()));
			} else {
				Iterator<Type> iter1 = argList.iterator();
				if (!func.isStatik()) {
					iter1.next();
				}
				Iterator<Tree.Expr> iter2 = callExpr.actuals.iterator();
				for (int i = 1; iter1.hasNext(); i++) {
					Type t1 = iter1.next();
					Tree.Expr e = iter2.next();
					Type t2 = e.type;
					if (!t2.equal(BaseType.ERROR) && !t2.compatible(t1)) {
						issueError(new BadArgTypeError(e.getLocation(), i, 
								t2.toString(), t1.toString()));
					}
				}
			}
		}
	}

	@Override
	public void visitCallExpr(Tree.CallExpr callExpr) {
		if (callExpr.receiver == null) {
			ClassScope cs = (ClassScope) table.lookForScope(Kind.CLASS);
			checkCallExpr(callExpr, cs.lookupVisible(callExpr.method));
			return;
		}
		callExpr.receiver.usedForRef = true;
		callExpr.receiver.accept(this);

		if (callExpr.receiver.type.equal(BaseType.ERROR)) {
			callExpr.type = BaseType.ERROR;
			return;
		}
		if (callExpr.method.equals("length")) {
			if (callExpr.receiver.type.isArrayType()) {
				if (callExpr.actuals.size() > 0) {
					issueError(new BadLengthArgError(callExpr.getLocation(),
							callExpr.actuals.size()));
				}
				callExpr.type = BaseType.INT;
				callExpr.isArrayLength = true;
				return;
			} else if (!callExpr.receiver.type.isClassType()) {
				issueError(new BadLengthError(callExpr.getLocation()));
				callExpr.type = BaseType.ERROR;
				return;
			}
		}

		if (!callExpr.receiver.type.isClassType()) {
			issueError(new NotClassFieldError(callExpr.getLocation(),
					callExpr.method, callExpr.receiver.type.toString()));
			//System.out.println("+++++++++++++++++++++++++++++++++++++++");
			callExpr.type = BaseType.ERROR;
			return;
		}

		ClassScope cs = ((ClassType) callExpr.receiver.type)
				.getClassScope();
		checkCallExpr(callExpr, cs.lookupVisible(callExpr.method));
	}

	@Override
	public void visitExec(Tree.Exec exec){
		exec.expr.accept(this);
	}
	
	@Override
	public void visitNewArray(Tree.NewArray newArrayExpr) {
		newArrayExpr.elementType.accept(this);
		if (newArrayExpr.elementType.type.equal(BaseType.ERROR)) {
			newArrayExpr.type = BaseType.ERROR;
		} else if (newArrayExpr.elementType.type.equal(BaseType.VOID)) {
			issueError(new BadArrElementError(newArrayExpr.elementType
					.getLocation()));
			newArrayExpr.type = BaseType.ERROR;
		} else {
			newArrayExpr.type = new ArrayType(
					newArrayExpr.elementType.type);
		}
		newArrayExpr.length.accept(this);
		if (!newArrayExpr.length.type.equal(BaseType.ERROR)
				&& !newArrayExpr.length.type.equal(BaseType.INT)) {
			issueError(new BadNewArrayLength(newArrayExpr.length.getLocation()));
		}
	}

	@Override
	public void visitNewClass(Tree.NewClass newClass) {
		Class c = table.lookupClass(newClass.className);
		newClass.symbol = c;
		if (c == null) {
			issueError(new ClassNotFoundError(newClass.getLocation(),
					newClass.className));
			newClass.type = BaseType.ERROR;
		} else {
			newClass.type = c.getType();
		}
	}

	@Override
	public void visitThisExpr(Tree.ThisExpr thisExpr) {
		if (currentFunction.isStatik()) {
			issueError(new ThisInStaticFuncError(thisExpr.getLocation()));
			thisExpr.type = BaseType.ERROR;
		} else {
			thisExpr.type = ((ClassScope) table.lookForScope(Scope.Kind.CLASS))
					.getOwner().getType();
		}
	}

	@Override
	public void visitTypeTest(Tree.TypeTest instanceofExpr) {
		instanceofExpr.instance.accept(this);
		if (!instanceofExpr.instance.type.isClassType()) {
			issueError(new NotClassError(instanceofExpr.instance.type
					.toString(), instanceofExpr.getLocation()));
		}
		Class c = table.lookupClass(instanceofExpr.className);
		instanceofExpr.symbol = c;
		instanceofExpr.type = BaseType.BOOL;
		if (c == null) {
			issueError(new ClassNotFoundError(instanceofExpr.getLocation(),
					instanceofExpr.className));
		}
	}

	@Override
	public void visitTypeCast(Tree.TypeCast cast) {
		cast.expr.accept(this);
		if (!cast.expr.type.isClassType()) {
			issueError(new NotClassError(cast.expr.type.toString(),
					cast.getLocation()));
		}
		Class c = table.lookupClass(cast.className);
		cast.symbol = c;
		if (c == null) {
			issueError(new ClassNotFoundError(cast.getLocation(),
					cast.className));
			cast.type = BaseType.ERROR;
		} else {
			cast.type = c.getType();
		}
	}

	@Override
	public void visitIdent(Tree.Ident ident) {
		if(!ident.var) {
			if (ident.owner == null) {
				Symbol v = table.lookupBeforeLocation(ident.name, ident
						.getLocation());
				if (v == null) {
					issueError(new UndeclVarError(ident.getLocation(), ident.name));
					ident.type = BaseType.ERROR;
				} else if (v.isVariable()) {
					Variable var = (Variable) v;
					ident.type = var.getType();
					ident.symbol = var;
					if (var.isLocalVar()) {
						ident.lvKind = Tree.LValue.Kind.LOCAL_VAR;
					} else if (var.isParam()) {
						ident.lvKind = Tree.LValue.Kind.PARAM_VAR;
					} else {
						if (currentFunction.isStatik()) {
							issueError(new RefNonStaticError(ident.getLocation(),
									currentFunction.getName(), ident.name));
						} else {
							ident.owner = new Tree.ThisExpr(ident.getLocation());
							ident.owner.accept(this);
						}
						ident.lvKind = Tree.LValue.Kind.MEMBER_VAR;
					}
				} else {
					ident.type = v.getType();
					if (v.isClass()) {
						if (ident.usedForRef) {
							ident.isClass = true;
						} else {
							issueError(new UndeclVarError(ident.getLocation(),
									ident.name));
							ident.type = BaseType.ERROR;
						}

					}
				}
			} else {
				ident.owner.usedForRef = true;
				ident.owner.accept(this);
				if (!ident.owner.type.equal(BaseType.ERROR)) {
					if (ident.owner.isClass || !ident.owner.type.isClassType()) {
						issueError(new NotClassFieldError(ident.getLocation(),
								ident.name, ident.owner.type.toString()));

						ident.type = BaseType.ERROR;
					} else {
						ClassScope cs = ((ClassType) ident.owner.type)
								.getClassScope();
						Symbol v = cs.lookupVisible(ident.name);
						if (v == null) {
							issueError(new FieldNotFoundError(ident.getLocation(),
									ident.name, ident.owner.type.toString()));
							ident.type = BaseType.ERROR;
						} else if (v.isVariable()) {
							ClassType thisType = ((ClassScope) table
									.lookForScope(Scope.Kind.CLASS)).getOwner()
									.getType();
							ident.type = v.getType();
							if (!thisType.compatible(ident.owner.type)) {
								issueError(new FieldNotAccessError(ident
										.getLocation(), ident.name,
										ident.owner.type.toString()));
							} else {
								ident.symbol = (Variable) v;
								ident.lvKind = Tree.LValue.Kind.MEMBER_VAR;
							}
						} else {
							ident.type = v.getType();
						}
					}
				} else {
					ident.type = BaseType.ERROR;
				}
			}
		} else {
			/*Symbol symbol = table.lookup(ident.name, true);
			if(symbol != null) {
				if(table.getCurrentScope().equals(symbol.getScope()))
					issueError(new DeclConflictError(ident.loc, ident.name, symbol.getLocation()));
				else if(symbol.getScope().isFormalScope() && table.getCurrentScope().isLocalScope() && ((LocalScope)table.getCurrentScope()).isCombinedtoFormal())
					issueError(new DeclConflictError(ident.loc, ident.name, symbol.getLocation()));
			}*/
			ident.type = BaseType.UNKNOWN;
		}

	}

	@Override
	public void visitClassDef(Tree.ClassDef classDef) {
		table.open(classDef.symbol.getAssociatedScope());
		if(classDef.sealed) {
			table.lookup(classDef.name, true).setSealed(true);
		}
		if(classDef.parent != null) {
			Symbol v = table.lookup(classDef.parent, true);
			if(v.getSealed()) {
				issueError(new BadSealedInherError(classDef.getLocation()));
			}
		}
		for (Tree f : classDef.fields) {
			f.accept(this);
		}
		table.close();
	}

	@Override
	public void visitMethodDef(Tree.MethodDef func) {
		this.currentFunction = func.symbol;
		table.open(func.symbol.getAssociatedScope());
		func.body.accept(this);
		table.close();
	}

	@Override
	public void visitTopLevel(Tree.TopLevel program) {
		table.open(program.globalScope);
		for (Tree.ClassDef cd : program.classes) {
			cd.accept(this);
		}
		table.close();
	}

	@Override
	public void visitBlock(Tree.Block block) {
		table.open(block.associatedScope);
		for (Tree s : block.block) {
			s.accept(this);
		}
		table.close();
	}

	@Override
	public void visitAssign(Tree.Assign assign) {
		assign.left.accept(this);
		assign.expr.accept(this);

		if(assign.left.type.equal(BaseType.UNKNOWN)) {
			Symbol symbol = table.lookup(((Tree.Ident)assign.left).name, false);
			assign.left.type = assign.expr.type;
			symbol.setType(assign.expr.type);
		}
		if (!assign.left.type.equal(BaseType.ERROR)
				&& (assign.left.type.isFuncType() || !assign.expr.type
						.compatible(assign.left.type))) {
			issueError(new IncompatBinOpError(assign.getLocation(),
					assign.left.type.toString(), "=", assign.expr.type
							.toString()));
		}
	}

	@Override
	public void visitBreak(Tree.Break breakStmt) {
		if (breaks.empty()) {
			issueError(new BreakOutOfLoopError(breakStmt.getLocation()));
		}
	}

	@Override
	public void visitForLoop(Tree.ForLoop forLoop) {
		if (forLoop.init != null) {
			forLoop.init.accept(this);
		}
		checkTestExpr(forLoop.condition);
		if (forLoop.update != null) {
			forLoop.update.accept(this);
		}
		breaks.add(forLoop);
		if (forLoop.loopBody != null) {
			forLoop.loopBody.accept(this);
		}
		breaks.pop();
	}

	@Override
	public void visitIf(Tree.If ifStmt) {
		checkTestExpr(ifStmt.condition);
		if (ifStmt.trueBranch != null) {
			ifStmt.trueBranch.accept(this);
		}
		if (ifStmt.falseBranch != null) {
			ifStmt.falseBranch.accept(this);
		}
	}

	@Override
	public void visitPrint(Tree.Print printStmt) {
		int i = 0;
		for (Tree.Expr e : printStmt.exprs) {
			e.accept(this);
			i++;
			if (!e.type.equal(BaseType.ERROR) && !e.type.equal(BaseType.BOOL)
					&& !e.type.equal(BaseType.INT)
					&& !e.type.equal(BaseType.STRING)) {
				issueError(new BadPrintArgError(e.getLocation(), Integer
						.toString(i), e.type.toString()));
			}
		}
	}

	@Override
	public void visitReturn(Tree.Return returnStmt) {
		Type returnType = ((FormalScope) table
				.lookForScope(Scope.Kind.FORMAL)).getOwner().getReturnType();
		if (returnStmt.expr != null) {
			returnStmt.expr.accept(this);
		}
		if (returnType.equal(BaseType.VOID)) {
			if (returnStmt.expr != null) {
				issueError(new BadReturnTypeError(returnStmt.getLocation(),
						returnType.toString(), returnStmt.expr.type.toString()));
			}
		} else if (returnStmt.expr == null) {
			issueError(new BadReturnTypeError(returnStmt.getLocation(),
					returnType.toString(), "void"));
		} else if (!returnStmt.expr.type.equal(BaseType.ERROR)
				&& !returnStmt.expr.type.compatible(returnType)) {
			issueError(new BadReturnTypeError(returnStmt.getLocation(),
					returnType.toString(), returnStmt.expr.type.toString()));
		}
	}

	@Override
	public void visitWhileLoop(Tree.WhileLoop whileLoop) {
		checkTestExpr(whileLoop.condition);
		breaks.add(whileLoop);
		if (whileLoop.loopBody != null) {
			whileLoop.loopBody.accept(this);
		}
		breaks.pop();
	}

	// visiting types
	@Override
	public void visitTypeIdent(Tree.TypeIdent type) {
		switch (type.typeTag) {
		case Tree.VOID:
			type.type = BaseType.VOID;
			break;
		case Tree.INT:
			type.type = BaseType.INT;
			break;
		case Tree.BOOL:
			type.type = BaseType.BOOL;
			break;
		case Tree.UNKNOWN:
			type.type = BaseType.UNKNOWN;
			break;
		default:
			type.type = BaseType.STRING;
		}
	}

	@Override
	public void visitTypeClass(Tree.TypeClass typeClass) {
		Class c = table.lookupClass(typeClass.name);
		if (c == null) {
			issueError(new ClassNotFoundError(typeClass.getLocation(),
					typeClass.name));
			typeClass.type = BaseType.ERROR;
		} else {
			typeClass.type = c.getType();
		}
	}

	@Override
	public void visitTypeArray(Tree.TypeArray typeArray) {
		typeArray.elementType.accept(this);
		if (typeArray.elementType.type.equal(BaseType.ERROR)) {
			typeArray.type = BaseType.ERROR;
		} else if (typeArray.elementType.type.equal(BaseType.VOID)) {
			issueError(new BadArrElementError(typeArray.getLocation()));
			typeArray.type = BaseType.ERROR;
		} else {
			typeArray.type = new ArrayType(typeArray.elementType.type);
		}
	}

	@Override
	public void visitScopy(Tree.Scopy scopy) {
		Symbol v = table.lookup(scopy.idName, true);
		if(v == null) {
			issueError(new UndeclVarError(scopy.idName_loc, scopy.idName));
			scopy.type = BaseType.ERROR;
		} else {
			scopy.instance.accept(this);
			if(!v.getType().isClassType()) {
				issueError(new BadScopyArgError(scopy.idName_loc, "dst", v.getType().toString()));
				scopy.type = BaseType.ERROR;
				if(!scopy.instance.type.isClassType()) {
					issueError(new BadScopyArgError(scopy.expr_loc, "src", scopy.instance.type.toString()));
				}
			} else {
				if(!(scopy.instance.type == v.getType())) {
					issueError(new BadScopySrcError(scopy.expr_loc, v.getType().toString(), scopy.instance.type.toString()));
				} // TODO check this message
				/*else
					scopy.type = v.getType();*/
			}
		}
	}

	@Override
	public void visitGuard(Tree.Guard guard) {
		if(!guard.empty) {
			if(guard.stmt_exist) {
				guard.expr.accept(this);
				guard.stmt.accept(this);
				if(!guard.expr.type.equal(BaseType.BOOL)) {
					issueError(new BadTestExpr(guard.expr.getLocation()));
				}
			} else if(guard.multi) {
				Tree.Guard stmt_ = (Tree.Guard) guard.ifsubstmt;
				stmt_.accept(this);
				/*stmt_.expr.accept(this);
				stmt_.stmt.accept(this);
				if(stmt_.expr.type.equal(BaseType.BOOL)) {
					issueError(new BadTestExpr(stmt_.expr.getLocation()));
				}*/
			} else if(guard.serial) {
				for(Tree s : guard.stmts) {
					//(Tree.Guard)s.expr.accept(this);
					Tree.Guard s_ = (Tree.Guard) s;
					s_.accept(this);
					//if(s_.expr.type.equal(BaseType.BOOL))
					//	issueError(new BadTestExpr(s_.expr.getLocation()));
				}
				Tree.Guard s_ = (Tree.Guard) guard.serialstmt;
				s_.accept(this);
				/*s_.expr.accept(this);
				s_.stmt.accept(this);
				if(s_.expr.type.equal(BaseType.BOOL))
					issueError(new BadTestExpr(s_.expr.getLocation()));*/
			}
		}
	}

	@Override
	public void visitArrayRepeat(Tree.ArrayRepeat arrayRepeat) {
		arrayRepeat.expr.accept(this);
		arrayRepeat.intconst.accept(this);
		boolean a = false;
		boolean b = false;
		if(arrayRepeat.expr.type.equal(BaseType.ERROR) ||
				arrayRepeat.expr.type.equal(BaseType.VOID) ||
				arrayRepeat.expr.type.equal(BaseType.UNKNOWN)) {
			issueError(new BadArrElementError(arrayRepeat.expr_loc));
			arrayRepeat.type = BaseType.ERROR;
			a = true;
		}
		if(!arrayRepeat.intconst.type.equal(BaseType.INT)) {
			issueError(new BadArrTimesError(arrayRepeat.intconst_loc));
			arrayRepeat.type = BaseType.ERROR;
			b = true;
		}
		if(!a && !b)
			arrayRepeat.type = new ArrayType(arrayRepeat.expr.type);
	}

	@Override
	public void visitDynamicAccess(Tree.DynamicAccess dynamicAccess) {
		dynamicAccess._1.accept(this);
		dynamicAccess._2.accept(this);
		dynamicAccess._3.accept(this);
		boolean _1_is_array = dynamicAccess._1.type.isArrayType();
		boolean _2_is_int = dynamicAccess._2.type.equal(BaseType.INT);
		boolean _3_type_equal_1 = false;
		if(_1_is_array)
			_3_type_equal_1 = dynamicAccess._3.type.equal(((ArrayType)dynamicAccess._1.type).getElementType());
		boolean _3_type_legal = !(dynamicAccess._3.type.equal(BaseType.ERROR) ||
				dynamicAccess._3.type.equal(BaseType.UNKNOWN) ||
				dynamicAccess._3.type.equal(BaseType.VOID));
		if(_1_is_array && _2_is_int && _3_type_equal_1) {
			dynamicAccess.type = ((ArrayType)dynamicAccess._1.type).getElementType();
		} else {
			if(!_1_is_array) {
				issueError(new BadArrOperArgError(dynamicAccess._1_loc));
			}
			if(!_2_is_int) {
				issueError(new BadArrIndexError(dynamicAccess._2_loc));
			}
			if(_1_is_array && !_3_type_equal_1) {
				issueError(new BadDefError(dynamicAccess._3_loc, ((ArrayType)dynamicAccess._1.type).getElementType().toString(), dynamicAccess._3.type.toString()));
				dynamicAccess.type = ((ArrayType)dynamicAccess._1.type).getElementType();
			}
			if(_1_is_array && !_2_is_int) {
				dynamicAccess.type = dynamicAccess._3.type;
			}
			if(!_1_is_array && _3_type_legal) {
				dynamicAccess.type = dynamicAccess._3.type;
			}
			if(!_1_is_array && !_3_type_legal) {
				dynamicAccess.type = BaseType.ERROR;
			}
		}
	}

	@Override
	public void visitForeach(Tree.Foreach foreach) {
		table.open(foreach.foreachblock.associatedScope);
		Tree _1 = foreach.foreachblock.block.get(0);
		_1.accept(this);
		Tree _2 = null;
		if(foreach._while) {
			_2 = foreach.foreachblock.block.get(1);
			_2.accept(this);
		}
		if(foreach.type instanceof Tree.TypeIdent && ((Tree.TypeIdent)foreach.type).typeTag == Tree.UNKNOWN) { // VAR
			if(!((Tree.Ident)_1).type.equal(BaseType.ERROR)) {
				if(!((Tree.Ident)_1).type.isArrayType()) {
					Variable v = new Variable(foreach.var_, BaseType.ERROR, foreach.x_loc);
					//foreach.symbol = new Variable(".error", BaseType.ERROR, foreach.x_loc);
					issueError(new BadArrOperArgError(foreach.e_loc));
					table.declare(v);
				} else {
					//System.out.println("**********************");
					Variable v = new Variable(foreach.var_, ((ArrayType)(((Tree.Ident)_1).type)).getElementType(), foreach.x_loc);
					//foreach.symbol = v;
					table.declare(v);
				}
			} else {
				Variable v = new Variable(foreach.var_, BaseType.ERROR, foreach.x_loc);
				//foreach.symbol = new Variable(".error", BaseType.ERROR, foreach.x_loc);
				//issueError(new BadArrOperArgError(foreach.loc));
				table.declare(v);
			}
		} else { //TYPE
			//System.out.println("name = " + ((Tree.Ident)_1).name);
			if(!((Tree.Ident)_1).type.isArrayType()) {
				issueError(new BadArrOperArgError(foreach.e_loc));
			}
		}
		if(foreach._while) {
			((Tree.Expr)_2).accept(this);
			if (!((Tree.Expr)_2).type.equal(BaseType.ERROR) && !((Tree.Expr)_2).type.equal(BaseType.BOOL)) {
				issueError(new BadTestExpr(((Tree.Expr)_2).getLocation()));
			}
		}
		breaks.add(foreach);
		for(int i=2;i<foreach.foreachblock.block.size();i++) {
			foreach.foreachblock.block.get(i).accept(this);
		}
		breaks.pop();
		table.close();
	}

	private void issueError(DecafError error) {
		Driver.getDriver().issueError(error);
	}

	private Type checkBinaryOp(Tree.Expr left, Tree.Expr right, int op, Location location) {
		left.accept(this);
		right.accept(this);

		if (left.type.equal(BaseType.ERROR) || right.type.equal(BaseType.ERROR)) {
			switch (op) {
			case Tree.PLUS:
			case Tree.MINUS:
			case Tree.MUL:
			case Tree.DIV:
				return left.type;
			case Tree.MOD:
				return BaseType.INT;
			default:
				return BaseType.BOOL;
			}
		}

		boolean compatible = false;
		Type returnType = BaseType.ERROR;
		switch (op) {
		case Tree.PLUS:
		case Tree.MINUS:
		case Tree.MUL:
		case Tree.DIV:
			compatible = left.type.equals(BaseType.INT)
					&& left.type.equal(right.type);
			returnType = left.type;
			break;
		case Tree.GT:
		case Tree.GE:
		case Tree.LT:
		case Tree.LE:
			compatible = left.type.equal(BaseType.INT)
					&& left.type.equal(right.type);
			returnType = BaseType.BOOL;
			break;
		case Tree.MOD:
			compatible = left.type.equal(BaseType.INT)
					&& right.type.equal(BaseType.INT);
			returnType = BaseType.INT;
			break;
		case Tree.EQ:
		case Tree.NE:
			compatible = left.type.compatible(right.type)
					|| right.type.compatible(left.type);
			returnType = BaseType.BOOL;
			break;
		case Tree.AND:
		case Tree.OR:
			compatible = left.type.equal(BaseType.BOOL)
					&& right.type.equal(BaseType.BOOL);
			returnType = BaseType.BOOL;
			break;
		default:
			break;
		}

		if (!compatible) {
			issueError(new IncompatBinOpError(location, left.type.toString(),
					Parser.opStr(op), right.type.toString()));
		}
		return returnType;
	}

	private void checkTestExpr(Tree.Expr expr) {
		expr.accept(this);
		if (!expr.type.equal(BaseType.ERROR) && !expr.type.equal(BaseType.BOOL)) {
			issueError(new BadTestExpr(expr.getLocation()));
		}
	}

}
