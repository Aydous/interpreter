#include "../include/KaleidoscopeJIT.h"
#include "llvm/IR/Verifier.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/APSInt.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/ExecutionEngine/MCJIT.h"
#include <algorithm>
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <vector>



using namespace llvm;
using namespace llvm::orc;

static int emitIR = 0;
static int emitObj = 0; //如果添加了-obj选项，则只生成.o文件，不运行代码
static char *inputFileName;

	
/*============================================================
                                                             |
                    the Lexer                                |
                                                             |
==============================================================*/
enum Token
{
	TOK_EOF = -1,
	ERROR = -2,
	VARIABLE = -3,
	INTEGER = -4,
	TEXT = -5,//
	ASSIGN_SYMBOL = -6,
	FUNC = -7,
	PRINT = -8,
	RETURN = -9,
	CONTINUE = -10,
	IF = -11,
	THEN = -12,
	ELSE = -13,
	FI = -14,
	WHILE = -15,
	DO = -16,
	DONE = -17,
	VAR = -18,
};

static std::string IdentifierStr;
static int NumberVal;
static FILE *inputFile;

/*
*返回输入单词类型
*/
static int gettok()
{
	static int LastChar = ' ';

	//过滤空格
	while(isspace(LastChar))
		LastChar = fgetc(inputFile);

	//解析标识符:{lc_letter}({lc_letter}|{digit})*
	if(isalpha(LastChar))
	{
		IdentifierStr = "";
		IdentifierStr += LastChar;
		while (isalnum((LastChar = fgetc(inputFile))))
			IdentifierStr += LastChar;

		if(IdentifierStr == "FUNC")
			return FUNC;
		if(IdentifierStr == "PRINT")
			return PRINT;
		if(IdentifierStr == "RETURN")
			return RETURN;
		if(IdentifierStr == "CONTINUE")
			return CONTINUE;
		if(IdentifierStr == "IF")
			return IF;
		if(IdentifierStr == "THEN")
			return THEN;
		if(IdentifierStr == "ELSE")
			return ELSE;
		if(IdentifierStr == "FI")
			return FI;
		if(IdentifierStr == "WHILE")
			return WHILE;
		if(IdentifierStr == "DO")
			return DO;
		if(IdentifierStr == "DONE")
			return DONE;
		if(IdentifierStr == "VAR")
			return VAR;

		return VARIABLE;	//非预留关键字，而是标识符
	}

	//解析整数:{digit}+
	if(isdigit(LastChar))
	{
		std::string NumStr;
		do{
			NumStr += LastChar;
			LastChar = fgetc(inputFile);
		}while(isdigit(LastChar));

		NumberVal = atoi(NumStr.c_str());

		return INTEGER;
	}

	//解析注释:"//".*
	if(LastChar == '/')
		if ((LastChar = fgetc(inputFile)) == '/')
		{
            do
				LastChar = fgetc(inputFile);
			while(LastChar != EOF && LastChar != '\n' && LastChar != '\r');

            //若未到达结尾，返回下一个输入类型
            if(LastChar != EOF)
                return gettok();
        }else{
            return '/';
        }

	//赋值符号
	if (LastChar == ':' && (LastChar = fgetc(inputFile)) == '=')
	{
		LastChar = fgetc(inputFile); //获取下一个字符
		return ASSIGN_SYMBOL;
	}

	//TEXT
	if(LastChar == '\"')
	{
        IdentifierStr = "";
		LastChar = fgetc(inputFile);
		do
		{
            if(LastChar == '\\')
            {
				LastChar = fgetc(inputFile);
				if(LastChar == 'n')
                    LastChar = '\n';
                else if(LastChar == 't')
                    LastChar = '\t';
                else if(LastChar == 'r')
                    LastChar = '\r';
                else
                    IdentifierStr += '\\';
            }
			IdentifierStr += LastChar;
			LastChar = fgetc(inputFile);
		}while(LastChar != '\"');
		LastChar = fgetc(inputFile);
		return TEXT;
	}

	if(LastChar == '\\')
    {
        int tmp;
		LastChar = fgetc(inputFile);
		if(LastChar == 'n')
            tmp = '\n';
        else if(LastChar == 't')
            tmp = '\t';
        else if(LastChar == 'r')
            tmp = '\r';
        else
            return '\\';
		LastChar = fgetc(inputFile);

		return tmp;
    }

	//文档结束标志
	if(LastChar == EOF)
		return TOK_EOF;

	//以上情况均不满足，直接返回当前字符
	int tmpChar = LastChar;
	LastChar = fgetc(inputFile);

	return tmpChar;
}
/*===================================================================
   AST of vsl
======================================================================*/
Function *printFunc;	//printf函数声明

class PrototypeAST;
Function *getFunction(std::string Name);
static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction,
	const std::string &VarName);

	//IR 部分
	static LLVMContext TheContext;
	static IRBuilder<> Builder(TheContext);
	std::unique_ptr<Module> Owner(new Module("test", TheContext));
	static /*std::unique_ptr<Module>*/Module * TheModule;

	static std::map<std::string, AllocaInst *> NamedValues;

	static std::unique_ptr<legacy::FunctionPassManager> TheFPM;
	static std::unique_ptr<KaleidoscopeJIT> TheJIT;
	//包含每个元素的最新原型
	static std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;

	//表达式抽象语法树基类
	class ExprAST {
	public:
		virtual ~ExprAST() = default;
		virtual Value *codegen() = 0;
	};

	/*statement部分 -- lh*/
	//statement 基类
	class StatAST {
	public:
		virtual ~StatAST() = default;
		virtual Value* codegen() = 0;
	};

	std::unique_ptr<StatAST> LogError(const char *Str);

	//report errors found during code generation
	Value *LogErrorV(const char *Str) {
		LogError(Str);
		return nullptr;
	}

	//数字抽象语法树
	class NumberExprAST : public StatAST {
		int Val;

	public:
		NumberExprAST(int Val) : Val(Val) {}

		Value * codegen() {
			return ConstantInt::get(TheContext, APInt(32,Val,true));
		}
	};

	//变量抽象语法树
	class VariableExprAST : public StatAST {
		std::string Name;

	public:
		std::string getName() {
			return Name;
		}

		VariableExprAST(const std::string &Name) : Name(Name) {}

		Value * codegen() {
			// Look this variable up in the function.
			Value *V = NamedValues[Name];
			if (!V)
				return LogErrorV("Unknown variable name");
			return Builder.CreateLoad(V, Name.c_str());
		}
	};

	class NegExprAST : public StatAST {
		std::unique_ptr<StatAST> EXP;

		public:
			NegExprAST(std::unique_ptr<StatAST> EXP)
				: EXP(std::move(EXP)) {
			}

			Value * codegen() {
				auto Value = EXP->codegen();
				if (!Value)
					return nullptr;

				return Builder.CreateNeg(Value);
			}
	};

	//'+','-','*','/'二元运算表达式抽象语法树
	class BinaryExprAST : public StatAST {
		char Op;
		std::unique_ptr<StatAST> LHS, RHS;

	public:
		BinaryExprAST(char Op, std::unique_ptr<StatAST> LHS,
			std::unique_ptr<StatAST> RHS)
			: Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}


		Value * codegen() {

			Value *L = LHS->codegen();
			Value *R = RHS->codegen();
			if (!L || !R)
				return nullptr;

			switch (Op) {
			case '+':
				return Builder.CreateAdd(L, R, "addtmp");
			case '-':
				return Builder.CreateSub(L, R, "subtmp");
			case '*':
				return Builder.CreateMul(L, R, "multmp");
			case '/':
				L = Builder.CreateExactSDiv(L, R, "divtmp");
				// Convert bool 0/1 to int 0 or 1
				return Builder.CreateUIToFP(L, Type::getInt32Ty(TheContext), "booltmp");
			default:
				return LogErrorV("invalid binary operator");
			}
		}
	};

	//函数原型抽象语法树--函数名和参数列表
	class PrototypeAST {
		std::string Name;
		std::vector<std::string> Args;

	public:
		PrototypeAST(const std::string &Name, std::vector<std::string> Args)
			: Name(Name), Args(std::move(Args)) {}

		const std::string &getName() const { return Name; }

		Function * codegen() {
			//不允许函数重定义
			Function *TheFunction = TheModule->getFunction(Name);
			if (TheFunction)
				return (Function*)LogErrorV("Function cannot be redefined.");

			// 函数形参类型为 int
			std::vector<Type*> Integers(Args.size(),
				Type::getInt32Ty(TheContext));
			FunctionType *FT =
				FunctionType::get(Type::getInt32Ty(TheContext), Integers, false);

			// 注册该函数
			Function *F =
				Function::Create(FT, Function::ExternalLinkage, Name, TheModule);

			// 为函数参数命名
			unsigned Idx = 0;
			for (auto &Arg : F->args())
				Arg.setName(Args[Idx++]);

			return F;
		}
	};

	// CreateEntryBlockAlloca - Create an alloca instruction in the entry block of
	// the function.  This is used for mutable variables etc.
	static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction,
		const std::string &VarName) {
		IRBuilder<> TmpB(&TheFunction->getEntryBlock(),
			TheFunction->getEntryBlock().begin());
		return TmpB.CreateAlloca(Type::getInt32Ty(TheContext), nullptr,
			VarName.c_str());
	}

	//空语句
	class NullStatAST:public StatAST {
	public:
		Value *codegen() {

		}
	};

	//变量声明语句
	class DecAST : public StatAST {
		std::vector<std::string> VarNames;
		std::unique_ptr<StatAST> Body;

	public:
		DecAST(std::vector<std::string> VarNames, std::unique_ptr<StatAST> Body)
			:VarNames(std::move(VarNames)), Body(std::move(Body)) {}

		Value *codegen() {
			std::vector<AllocaInst *> OldBindings;

			Function *TheFunction = Builder.GetInsertBlock()->getParent();

			for (unsigned i = 0, e = VarNames.size(); i != e; ++i) {
				const std::string &VarName = VarNames[i];

				Value *InitVal = ConstantInt::get(TheContext, APInt(32,0));

				AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, VarName);
				Builder.CreateStore(InitVal, Alloca);

				OldBindings.push_back(NamedValues[VarName]);
				NamedValues[VarName] = Alloca;
			}

			return nullptr;
		}
	};

	//块语句
	class BlockStatAST : public StatAST {
		std::vector<std::unique_ptr<DecAST>> DecList;
		std::vector<std::unique_ptr<StatAST>> StatList;

	public:
		BlockStatAST(std::vector<std::unique_ptr<DecAST>> DecList, std::vector<std::unique_ptr<StatAST>> StatList)
			:DecList(std::move(DecList)), StatList(std::move(StatList)){}

	public:
		Value* codegen()
		{
			for (int i = 0; i < DecList.size(); i++)
			{
				DecList[i]->codegen();
			}
			for (int j = 0; j < StatList.size(); j++)
			{
				StatList[j]->codegen();
			}
			return Builder.getInt32(0); //block always return 0
		}
	};

	//Text //暂时不用--MT
	class TextAST {

	};

	class PrintStatAST : public StatAST {
        std::string text;
		std::vector<std::unique_ptr<StatAST>> expr;

	  public:
        PrintStatAST(std::string text, std::vector<std::unique_ptr<StatAST>> expr):
            text(text), expr(std::move(expr)){}
        Value *codegen()
        {
			Function *TheFunction = Builder.GetInsertBlock()->getParent();

            std::vector<llvm::Value *> paramArrayRef;
            Value *intFormat = Builder.CreateGlobalStringPtr(text.c_str());
            paramArrayRef.push_back(intFormat);

			for (int i = 0; i<expr.size(); i++)//auto tmp = expr.begin(); tmp != expr.end(); tmp++)
			{
				Value *tmpValue = expr[i]->codegen();
				paramArrayRef.push_back(tmpValue);
			}

			Builder.CreateCall(printFunc, paramArrayRef);

			Value *num = Builder.getInt32(0);//print always return 0
			return num;
        }
	};

	//IF Statement
	class IfStatAST : public StatAST {
		std::unique_ptr<StatAST> Cond;
		std::unique_ptr<StatAST> Then, Else;

	public:
		IfStatAST(std::unique_ptr<StatAST> Cond, std::unique_ptr<StatAST> Then,
			std::unique_ptr<StatAST> Else)
			: Cond(std::move(Cond)), Then(std::move(Then)), Else(std::move(Else)) {}

		Value *codegen() {
			Value *CondV = Cond->codegen();
			if (!CondV)
				return nullptr;

			// Convert condition to a bool by comparing non-equal to 0.0.
			CondV = Builder.CreateICmpNE(
				CondV, Builder.getInt32(0), "ifcond");

			Function *TheFunction = Builder.GetInsertBlock()->getParent();

			// Create blocks for the then and else cases.  Insert the 'then' block at the
			// end of the function.
			BasicBlock *ThenBB = BasicBlock::Create(TheContext, "then", TheFunction);
			BasicBlock *MergeBB = BasicBlock::Create(TheContext, "ifcont");
			BasicBlock *ElseBB = nullptr;
			if (Else != nullptr) {
				ElseBB = BasicBlock::Create(TheContext, "else");
				Builder.CreateCondBr(CondV, ThenBB, ElseBB);
			}
			else {
				Builder.CreateCondBr(CondV, ThenBB, MergeBB);
			}

			// Emit then value.
			Builder.SetInsertPoint(ThenBB);

			Value *ThenV = Then->codegen();
			if (!ThenV)
				return nullptr;

			Builder.CreateBr(MergeBB);
			// Codegen of 'Then' can change the current block, update ThenBB for the PHI.
			ThenBB = Builder.GetInsertBlock();

			// Emit else block.
			if (ElseBB != nullptr) {
				TheFunction->getBasicBlockList().push_back(ElseBB);
				Builder.SetInsertPoint(ElseBB);

				Value *ElseV = Else->codegen();
				if (!ElseV)
					return nullptr;
				Builder.CreateBr(MergeBB);

				// Codegen of 'Else' can change the current block, update ElseBB for the PHI.
				ElseBB = Builder.GetInsertBlock();
			}

			// Emit merge block.
			TheFunction->getBasicBlockList().push_back(MergeBB);
			Builder.SetInsertPoint(MergeBB);

			return nullptr;
		}

	};

	class RetStatAST : public StatAST {
		std::unique_ptr<StatAST> Val;

		public:
			RetStatAST(std::unique_ptr<StatAST> Val)
				: Val(std::move(Val)) {}

			Value *codegen() {
				Function *TheFunction = Builder.GetInsertBlock()->getParent();
				if (Value *RetVal = Val->codegen()) {
					Builder.CreateRet(RetVal);
					BasicBlock *afterRet = BasicBlock::Create(TheContext, "afterReturn", TheFunction);
					Builder.SetInsertPoint(afterRet);

					return RetVal;
				}
			}
	};

	class AssStatAST : public StatAST {
		std::unique_ptr<VariableExprAST> Name;
		std::unique_ptr<StatAST> Expression;

	public:
		AssStatAST(std::unique_ptr<VariableExprAST> Name, std::unique_ptr<StatAST> Expression)
			: Name(std::move(Name)), Expression(std::move(Expression)) {}

		Value *codegen() {
			Value* EValue = Expression->codegen();
			if (!EValue)
				return nullptr;

			Value *Variable = NamedValues[Name->getName()];
			if (!Variable)
				return LogErrorV("Unknown variable name");

			Builder.CreateStore(EValue, Variable);

			return EValue;
		}
	};

	//函数抽象语法树
	class FunctionAST {
		std::unique_ptr<PrototypeAST> Proto;
		std::unique_ptr<StatAST> Body;

	public:
		FunctionAST(std::unique_ptr<PrototypeAST> Proto,
			std::unique_ptr<StatAST> Body)
			: Proto(std::move(Proto)), Body(std::move(Body)) {}

		Function * codegen() {
			//可在当前模块中获取任何先前声明的函数的函数声明
			auto &P = *Proto;
			FunctionProtos[Proto->getName()] = std::move(Proto);
			Function *TheFunction = getFunction(P.getName());
			if (!TheFunction)
				return nullptr;

			// Create a new basic block to start insertion into.
			BasicBlock *BB = BasicBlock::Create(TheContext, "entry", TheFunction);
			Builder.SetInsertPoint(BB);

			// Record the function arguments in the NamedValues map.
			NamedValues.clear();
			for (auto &Arg : TheFunction->args()) {

				// Create an alloca for this variable.
				AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, Arg.getName());

				// Store the initial value into the alloca.
				Builder.CreateStore(&Arg, Alloca);

				// Add arguments to variable symbol table.
				NamedValues[Arg.getName()] = Alloca;
			}

			Body->codegen();

			Builder.CreateRet(Builder.getInt32(0)); //如果函数没有返回语句，添加个RETURN 0
			verifyFunction(*TheFunction);

			return TheFunction;
		}
	};

	//函数调用抽象语法树
	class CallExprAST : public StatAST {
		std::string Callee;
		std::vector<std::unique_ptr<StatAST>> Args;
	public:
		CallExprAST(const std::string &Callee,
			std::vector<std::unique_ptr<StatAST>> Args)
			: Callee(Callee), Args(std::move(Args)) {}

		Value * codegen() {
			// Look up the name in the global module table.
			Function *CalleeF = getFunction(Callee);
			if (!CalleeF)
				return LogErrorV("Unknown function referenced");

			// If argument mismatch error.
			if (CalleeF->arg_size() != Args.size())
				return LogErrorV("Incorrect # arguments passed");

			std::vector<Value *> ArgsV;
			for (unsigned i = 0, e = Args.size(); i != e; ++i) {
				ArgsV.push_back(Args[i]->codegen());
				if (!ArgsV.back())
					return nullptr;
			}

			return Builder.CreateCall(CalleeF, ArgsV, "calltmp");
		}
	};


	//程序的抽象语法树
	class ProgramAST {
		std::vector<std::unique_ptr<FunctionAST>> funcs;

	public:
		ProgramAST(std::vector<std::unique_ptr<FunctionAST>> funcs)
			:funcs(std::move(funcs)) {}
	};

	class WhileStatAST:public StatAST{
		std::unique_ptr<StatAST> Expr, Stat;
	public:
		WhileStatAST(std::unique_ptr<StatAST> Expr, std::unique_ptr<StatAST> Stat):
			Expr(std::move(Expr)), Stat(std::move(Stat)){}
		
		Value *codegen()
		{
			Function *TheFunction = Builder.GetInsertBlock()->getParent();
			BasicBlock *LoopBB = BasicBlock::Create(TheContext, "loop", TheFunction);
			BasicBlock *AfterBB = BasicBlock::Create(TheContext, "afterLoop", TheFunction);

			Value *EndCond = Expr->codegen();
			if(!EndCond)
				return nullptr;
			EndCond = Builder.CreateICmpNE(EndCond, Builder.getInt32(0),
					"loopCondIn");
			Builder.CreateCondBr(EndCond, LoopBB, AfterBB);

			Builder.SetInsertPoint(LoopBB);
			Value *inLoopVal = Stat->codegen();
			if(!inLoopVal)
				return nullptr;
			EndCond = Builder.CreateICmpNE(Expr->codegen(), 
				Builder.getInt32(0), "loopCondOut");
			Builder.CreateCondBr(EndCond, LoopBB, AfterBB);

			Builder.SetInsertPoint(AfterBB);

			return Builder.getInt32(0);
		}
	};


	//创建和初始化模块和传递管理器
	static void InitializeModuleAndPassManager() {

		// Open a new module.
		TheModule = Owner.get();//llvm::make_unique<Module>("VSL jit", TheContext);
		TheModule->setDataLayout(TheJIT->getTargetMachine().createDataLayout());

		// Create a new pass manager attached to it.
		TheFPM = llvm::make_unique<legacy::FunctionPassManager>(TheModule);

		// Promote allocas to registers.
		TheFPM->add(createPromoteMemoryToRegisterPass());
		// Do simple "peephole" optimizations and bit-twiddling optzns.
		TheFPM->add(createInstructionCombiningPass());
		// Reassociate expressions.
		TheFPM->add(createReassociatePass());
		// Eliminate Common SubExpressions.
		TheFPM->add(createGVNPass());
		// Simplify the control flow graph (deleting unreachable blocks, etc).
		TheFPM->add(createCFGSimplificationPass());

		TheFPM->doInitialization();

	}

	Function *getFunction(std::string Name) {
		// First, see if the function has already been added to the current module.
		if (auto *F = TheModule->getFunction(Name))
			return F;

		// If not, check whether we can codegen the declaration from some existing
		// prototype.
		auto FI = FunctionProtos.find(Name);
		if (FI != FunctionProtos.end())
			return FI->second->codegen();

		// If no existing prototype exists, return null.
		return nullptr;
	}
/*============================================================
                                                             |
                       Parser of vsl                         |
                                                             |
==============================================================*/


static int CurTok;
static std::map<char, int> BinopPrecedence;
static int getNextToken() { return CurTok = gettok(); }

static std::unique_ptr<StatAST> ParseExpression();
std::unique_ptr<StatAST> LogError(const char *Str);
static std::unique_ptr<StatAST> ParseNumberExpr();
static std::unique_ptr<StatAST> ParseParenExpr();
static std::unique_ptr<DecAST> ParseDec();
std::unique_ptr<StatAST> LogError(const char *Str);
std::unique_ptr<PrototypeAST> LogErrorP(const char *Str);
std::unique_ptr<StatAST> LogErrorS(const char *Str);
std::unique_ptr<DecAST> LogErrorD(const char *Str);
static std::unique_ptr<StatAST> ParseStatement();

//解析如下格式的表达式：
// identifer || identifier(expression list)
static std::unique_ptr<StatAST> ParseIdentifierExpr() {
	std::string IdName = IdentifierStr;

	getNextToken();

	//解析成变量表达式
	if (CurTok != '(')
		return llvm::make_unique<VariableExprAST>(IdName);

	// 解析成函数调用表达式
	getNextToken();
	std::vector<std::unique_ptr<StatAST>> Args;
	if (CurTok != ')') {
		while (true) {
			if (auto Arg = ParseExpression())
				Args.push_back(std::move(Arg));
			else
				return nullptr;

			if (CurTok == ')')
				break;

			if (CurTok != ',')
				return LogErrorS("Expected ')' or ',' in argument list");
			getNextToken();
		}
	}

	getNextToken();

	return llvm::make_unique<CallExprAST>(IdName, std::move(Args));
}

//解析取反表达式
static std::unique_ptr<StatAST> ParseNegExpr() {
	getNextToken();
	std::unique_ptr<StatAST> Exp = ParseExpression();
	if (!Exp)
		return nullptr;

	return llvm::make_unique<NegExprAST>(std::move(Exp));
}

//解析成 标识符表达式、整数表达式、括号表达式中的一种
static std::unique_ptr<StatAST> ParsePrimary() {
	switch (CurTok) {
	default:
		return LogError("unknown token when expecting an expression");
	case VARIABLE:
		return ParseIdentifierExpr();
	case INTEGER:
		return ParseNumberExpr();
	case '(':
		return ParseParenExpr();
	case '-':
		return ParseNegExpr();
	}
}

//GetTokPrecedence - Get the precedence of the pending binary operator token.
static int GetTokPrecedence() {
  if (!isascii(CurTok))
    return -1;

  // Make sure it's a declared binop.
  int TokPrec = BinopPrecedence[CurTok];
  if (TokPrec <= 0)
    return -1;
  return TokPrec;
}

//解析二元表达式
//参数 ：
//ExprPrec 左部运算符优先级
//LHS 左部操作数
// 递归得到可以结合的右部，循环得到一个整体二元表达式
static std::unique_ptr<StatAST> ParseBinOpRHS(int ExprPrec,
	std::unique_ptr<StatAST> LHS) {

	while (true) {
		int TokPrec = GetTokPrecedence();

		// 当右部没有运算符或右部运算符优先级小于左部运算符优先级时 退出循环和递归
		if (TokPrec < ExprPrec)
			return LHS;

		if(CurTok == '}')
			return LHS;

		// 保存左部运算符
		int BinOp = CurTok;
		getNextToken();

		// 得到右部表达式
		auto RHS = ParsePrimary();
		if (!RHS)
			return nullptr;

		// 如果该右部表达式不与该左部表达式结合 那么递归得到右部表达式
		int NextPrec = GetTokPrecedence();
		if (TokPrec < NextPrec) {
			RHS = ParseBinOpRHS(TokPrec + 1, std::move(RHS));
			if (!RHS)
				return nullptr;
		}

		// 将左右部结合成新的左部
		LHS = llvm::make_unique<BinaryExprAST>(BinOp, std::move(LHS),
			std::move(RHS));
	}
}

// 解析得到表达式
static std::unique_ptr<StatAST> ParseExpression() {
	auto LHS = ParsePrimary();
	if (!LHS)
		return nullptr;

	return ParseBinOpRHS(0, std::move(LHS));
}

// numberexpr ::= number
static std::unique_ptr<StatAST> ParseNumberExpr() {
	auto Result = llvm::make_unique<NumberExprAST>(NumberVal);
	//略过数字获取下一个输入
	getNextToken();
	return std::move(Result);
}

//declaration::=VAR variable_list
static std::unique_ptr<DecAST> ParseDec() {
	//eat 'VAR'
	getNextToken();

	std::vector<std::string> varNames;
	//保证至少有一个变量的名字
	if (CurTok != VARIABLE) {
		return LogErrorD("expected identifier after VAR");
	}

	while (true)
	{
		varNames.push_back(IdentifierStr);
		//eat VARIABLE
		getNextToken();
		if (CurTok != ',')
			break;
		getNextToken();
		if (CurTok != VARIABLE) {
			return LogErrorD("expected identifier list after VAR");
		}
	}

	auto Body = nullptr;

	return llvm::make_unique<DecAST>(std::move(varNames), std::move(Body));
}

//null_statement::=CONTINUE
static std::unique_ptr<StatAST> ParseNullStat() {
	getNextToken();
	return nullptr;
}

//block::='{' declaration_list statement_list '}'
static std::unique_ptr<StatAST> ParseBlock() {
	//存储变量声明语句及其他语句
	std::vector<std::unique_ptr<DecAST>> DecList;
	std::vector<std::unique_ptr<StatAST>> StatList;
	getNextToken();   //eat '{'
	if (CurTok == VAR) {
		auto varDec = ParseDec();
		DecList.push_back(std::move(varDec));
	}
	while (CurTok != '}') {
		if (CurTok == VAR) {
			LogErrorS("Can't declare VAR here!");
		}
		else if (CurTok == '{') {
			ParseBlock();
		}
		else if (CurTok == CONTINUE) {
			getNextToken();
		}
		else {
			auto statResult = ParseStatement();
			StatList.push_back(std::move(statResult));
		}
	}
	getNextToken();  //eat '}'

	return llvm::make_unique<BlockStatAST>(std::move(DecList), std::move(StatList));
}

//prototype ::= VARIABLE '(' parameter_list ')'
static std::unique_ptr<PrototypeAST> ParsePrototype() {
	if (CurTok != VARIABLE)
		return LogErrorP("Expected function name in prototype");

	std::string FnName = IdentifierStr;
	getNextToken();

	if (CurTok != '(')
		return LogErrorP("Expected '(' in prototype");

	std::vector<std::string> ArgNames;
	getNextToken();
	while (CurTok == VARIABLE)
	{
		ArgNames.push_back(IdentifierStr);
		getNextToken();
		if (CurTok == ',')
			getNextToken();
	}
	if (CurTok != ')')
		return LogErrorP("Expected ')' in prototype");

	// success.
	getNextToken(); // eat ')'.

	return llvm::make_unique<PrototypeAST>(FnName, std::move(ArgNames));
}

//function ::= FUNC VARIABLE '(' parameter_lst ')' statement
static std::unique_ptr<FunctionAST> ParseFunc()
{
	getNextToken(); // eat FUNC.
	auto Proto = ParsePrototype();
	if (!Proto)
		return nullptr;

	auto E = ParseStatement();
	if (!E)
		return nullptr;

	return llvm::make_unique<FunctionAST>(std::move(Proto), std::move(E));
}

//解析括号中的表达式
static std::unique_ptr<StatAST> ParseParenExpr() {
	// 过滤'('
	getNextToken();
	auto V = ParseExpression();
	if (!V)
		return nullptr;

	if (CurTok != ')')
		return LogError("expected ')'");
	// 过滤')'
	getNextToken();
	return V;
}

//解析 IF Statement
static std::unique_ptr<StatAST> ParseIfStat() {
	getNextToken(); // eat the IF.

					// condition.
	auto Cond = ParseExpression();
	if (!Cond)
		return nullptr;

	if (CurTok != THEN)
		return LogErrorS("expected THEN");
	getNextToken(); // eat the THEN

	auto Then = ParseStatement();
	if (!Then)
		return nullptr;

	std::unique_ptr<StatAST> Else = nullptr;
	if (CurTok == ELSE) {
        getNextToken();
		Else = ParseStatement();
		if (!Else)
			return nullptr;
	}
	else if(CurTok != FI)
		return LogErrorS("expected FI or ELSE");

	getNextToken();

	return llvm::make_unique<IfStatAST>(std::move(Cond), std::move(Then),
		std::move(Else));
}

//PRINT,能输出变量和函数调用的值
static std::unique_ptr<StatAST> ParsePrintStat()
{
    std::string text = "";
	std::vector<std::unique_ptr<StatAST>> expr;
	getNextToken();//eat PRINT

    while(CurTok == VARIABLE || CurTok == TEXT || CurTok == '('
            || CurTok == '-' || CurTok == INTEGER)
    {
        if(CurTok == TEXT)
        {
            text += IdentifierStr;
            getNextToken();
        }
        else
        {
            text += " %d ";
			expr.push_back(std::move(ParseExpression()));
		}

        if(CurTok != ',')
            break;
        getNextToken(); //eat ','
    }

    return llvm::make_unique<PrintStatAST>(text, std::move(expr));
}

//解析 RETURN Statement
static std::unique_ptr<StatAST> ParseRetStat() {
	getNextToken();
	auto Val = ParseExpression();
	if (!Val)
		return nullptr;

	return llvm::make_unique<RetStatAST>(std::move(Val));
}

//解析 赋值语句
static std::unique_ptr<StatAST> ParseAssStat() {
	auto a = ParseIdentifierExpr();
	VariableExprAST* Name = (VariableExprAST*)a.get();
	auto NameV = llvm::make_unique<VariableExprAST>(Name->getName());
	if (!Name)
		return nullptr;
	if (CurTok != ASSIGN_SYMBOL)
		return LogErrorS("need := in assignment statment");
	getNextToken();

	auto Expression = ParseExpression();
	if (!Expression)
		return nullptr;

	return llvm::make_unique<AssStatAST>(std::move(NameV), std::move(Expression));
}

//解析while语句
static std::unique_ptr<StatAST> ParseWhileStat()
{
	getNextToken();//eat WHILE

	auto E = ParseExpression();
	if(!E)
		return nullptr;

	if(CurTok != DO)
		return LogErrorS("expect DO in WHILE statement");
	getNextToken();//eat DO

	auto S = ParseStatement();
	if(!S)
	return nullptr;

	if(CurTok != DONE)
		return LogErrorS("expect DONE in WHILE statement");
	getNextToken();//eat DONE

	return llvm::make_unique<WhileStatAST>(std::move(E), std::move(S));
}

static std::unique_ptr<StatAST> ParseStatement()
{
	switch (CurTok) {
		case IF:
			return ParseIfStat();
			break;
        case PRINT:
            return ParsePrintStat();
		case RETURN:
			return ParseRetStat();
		case VAR:
			return ParseDec();
			break;
		case '{':
			return ParseBlock();
			break;
		case CONTINUE:
			return ParseNullStat();
		case WHILE:
			return ParseWhileStat();
			break;
		default:
			auto E = ParseAssStat();
			return E;
	}
}

//解析程序结构
static std::unique_ptr<ProgramAST> ParseProgramAST() {
	//接受程序中函数的语法树
	std::vector<std::unique_ptr<FunctionAST>> Functions;

	//循环解析程序中所有函数
	while (CurTok != TOK_EOF) {
		auto Func=ParseFunc();
		Functions.push_back(std::move(Func));
	}

	return llvm::make_unique<ProgramAST>(std::move(Functions));
}

//错误信息打印
std::unique_ptr<StatAST> LogError(const char *Str) {
	fprintf(stderr, "Error: %s\n", Str);
	return nullptr;
}
std::unique_ptr<PrototypeAST> LogErrorP(const char *Str) {
	LogError(Str);
	return nullptr;
}
std::unique_ptr<StatAST> LogErrorS(const char *Str) {
	fprintf(stderr, "Error: %s\n", Str);
	return nullptr;
}
std::unique_ptr<DecAST> LogErrorD(const char *Str) {
	fprintf(stderr, "Error: %s\n", Str);
	return nullptr;
}

// Top-Level parsing
static void HandleFuncDefinition() {
	if (auto FnAST = ParseFunc()) {
		FnAST->codegen();
	}
	else {
		// Skip token for error recovery.
		getNextToken();
	}
}

//声明printf函数
static void DeclarePrintfFunc()
{
	std::vector<llvm::Type *> printf_arg_types;
	printf_arg_types.push_back(Builder.getInt8Ty()->getPointerTo());
	FunctionType *printType = FunctionType::get(
		IntegerType::getInt32Ty(TheContext), printf_arg_types, true);
	printFunc = llvm::Function::Create(printType, llvm::Function::ExternalLinkage,
									   llvm::Twine("printf"), TheModule);
	printFunc->setCallingConv(llvm::CallingConv::C);

	std::vector<std::string> ArgNames;
	FunctionProtos["printf"] = std::move(llvm::make_unique<PrototypeAST>("printf", std::move(ArgNames)));
}

//program ::= function_list
static void MainLoop() {
	DeclarePrintfFunc();
	while(CurTok != TOK_EOF)
		HandleFuncDefinition();

	if (emitIR)
	{
		std::string IRstr;
		FILE *IRFile = fopen("IRCode.ll", "w");
		raw_string_ostream *rawStr = new raw_string_ostream(IRstr);
		TheModule->print(*rawStr, nullptr);
		fprintf(IRFile, "%s\n", rawStr->str().c_str());
	}

	if(!emitObj)
	{
		Function *main = getFunction("main");
		if (!main)
			printf("main is null");
		std::string errStr;
		ExecutionEngine *EE = EngineBuilder(std::move(Owner)).setErrorStr(&errStr).create();
		if (!EE)
		{
			errs() << "Failed to construct ExecutionEngine: " << errStr << "\n";
			return;
		}
		std::vector<GenericValue> noarg;
		GenericValue gv = EE->runFunction(main, noarg);
	}
}

	
/*============================================================
                                                             |
                      main  code                             |
                                                             |
==============================================================*/


void usage()
{
    printf("usage: VSL inputFile [-r] [-h]\n");
    printf("-r emit IR code to IRcode.ll file\n");
    printf("-h show help information\n");
    printf("-obj emit obj file of the input file\n");

    exit(EXIT_FAILURE);
}

void getArgs(int argc, char *argv[])
{
    for(int i = 1; i<argc; i++)
    {
        if(argv[i][0] == '-' && argv[i][1] == 'r')
        {
            emitIR = 1;
        }else if (argv[i][0] == '-' && argv[i][1] == 'h')
        {
            usage();
        }
        else if (argv[i][0] == '-' && argv[i][1] == 'o')
        {
            if (strlen(argv[i]) > 3 && 
                (argv[i][2] == 'b' && argv[i][3] == 'j'))
                emitObj = 1;
            else
                usage();
        }else
        {
            inputFileName = argv[i];
        }
    }
}

int main(int argc, char *argv[]) {
    if(argc < 2)
        usage();
    getArgs(argc, argv);
    inputFile = fopen(inputFileName, "r");
    if(!inputFile){
        printf("%s open error!\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();
    InitializeNativeTargetAsmParser();

    BinopPrecedence['+'] = 10;
    BinopPrecedence['-'] = 10;
    BinopPrecedence['*'] = 40;
    BinopPrecedence['/'] = 40;

    TheJIT = llvm::make_unique<KaleidoscopeJIT>();
    InitializeModuleAndPassManager();

    // Run the main "interpreter loop" now.
    getNextToken();
    MainLoop();

    if(emitObj)
    {
        // Initialize the target registry etc.
        InitializeAllTargetInfos();
        InitializeAllTargets();
        InitializeAllTargetMCs();
        InitializeAllAsmParsers();
        InitializeAllAsmPrinters();

        auto TargetTriple = sys::getDefaultTargetTriple();
        TheModule->setTargetTriple(TargetTriple);

        std::string Error;
        auto Target = TargetRegistry::lookupTarget(TargetTriple, Error);

        // Print an error and exit if we couldn't find the requested target.
        // This generally occurs if we've forgotten to initialise the
        // TargetRegistry or we have a bogus target triple.
        if (!Target)
        {
            errs() << Error;
            return 1;
        }

        auto CPU = "generic";
        auto Features = "";

        TargetOptions opt;
        auto RM = Optional<Reloc::Model>();
        auto TheTargetMachine =
            Target->createTargetMachine(TargetTriple, CPU, Features, opt, RM);

        TheModule->setDataLayout(TheTargetMachine->createDataLayout());

        auto Filename = "output.o";
        std::error_code EC;
        raw_fd_ostream dest(Filename, EC, sys::fs::F_None);

        if (EC)
        {
            errs() << "Could not open file: " << EC.message();
            return 1;
        }

        legacy::PassManager pass;
        auto FileType = TargetMachine::CGFT_ObjectFile;

        if (TheTargetMachine->addPassesToEmitFile(pass, dest, FileType))
        {
            errs() << "TheTargetMachine can't emit a file of this type";
            return 1;
        }

        pass.run(*TheModule);
        dest.flush();

        outs() << "Wrote " << Filename << "\n";
    }

    return 0;
}
