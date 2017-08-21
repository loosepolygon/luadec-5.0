#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>

#include "ldebug.h"
#include "lobject.h"
#include "lopcodes.h"
#include "lundump.h"
#include "lstring.h"
#include "lmem.h"

#include "StringBuffer.h"
#include "structs.h"
#include "proto.h"

#define DEBUG_PRINT

#define MAX(a,b) (((a)>(b))?(a):(b))
#define MIN(a,b) (((a)<(b))?(a):(b))

#define T int
#include "macro-array.h"
#undef T

#define T LocalData
#include "macro-array.h"
#undef T

#define last(l) (l.values[l.size-1])
#define addi(l, i) intArray_Push(&l, i)

#define FUNC_BLOCK_END(f) (f->sizecode - 1)
#define NEED_ARG(f) (((f->is_vararg == 3) || (f->is_vararg == 7))?1:0)
#define ISK(x) (x >= MAXSTACK)

int luaU_guess_locals(lua_State* luaState, Proto* f, int main) {
	// List of end PCs
	intArray blocklist;
	// Result
	LocalDataArray localList;
	// Start PCs for current registers. Locals start at the instruction
	// *after* they're declared.
	int regassign[MAXARG_A+1];
	// Counter of when registers are loaded from, such as the register
	// that OP_MOVE uses to get its value from
	int regusage[MAXARG_A+1];
	// End PCs for current registers. Locals end on the instruction that
	// their block ends, such as the first instruction after an if/else
	// block, or on OP_RETURN. (Need to test a bit more)
	int regblock[MAXARG_A+1];
	// Next available register slot that's unused
	int lastfree;
	int i,i2,x,pc;
	int func_endpc = FUNC_BLOCK_END(f);
	// Only used with OP_SETLIST, which looks complex
	int ignoreNext = 0;
	// These two are for assigning upvalues to closures
	int currentClosureIndex = -1;
	int upvaluesToEat = -1;

	if (f->lineinfo != NULL) {
		return 0;
	}

	if (f->sizelocvars > 0) {
		return 0;
	}

	intArray_Init(&blocklist, MAXARG_A+1);
	addi(blocklist, func_endpc);

	LocalDataArray_Init(&localList, MAXARG_A+1);

	lastfree = 0;
	for (i=0; i<f->maxstacksize; i++) {
		regassign[i] = 0;
		regusage[i] = 0;
		regblock[i] = 0;
	}

	// parameters
	for (i = 0; i < f->numparams; i++) {
		regassign[lastfree] = 0;
		regusage[lastfree] = 1;
		regblock[lastfree] = func_endpc;

		LocalData local;
		local.startpc = 0;
		local.endpc = func_endpc;
		local.reg = i;
		sprintf(local.name, "l_%d_arg%d", main, i);
		LocalDataArray_Push(&localList, local);

		lastfree++;
	}

	// vararg
	if (NEED_ARG(f)) {
		LocalData local;
		local.startpc = 0;
		local.endpc = func_endpc;
		local.reg = i;
		sprintf(local.name, "l_%d_vararg%d", main, i);
		LocalDataArray_Push(&localList, local);

		lastfree++;
	}

#ifdef OwO
	// nil optimizations
	{
		Instruction i = f->code[0];
		OpCode o = GET_OPCODE(i);
		int a = GETARG_A(i);
		int b = GETARG_B(i);
		int c = GETARG_C(i);
		int ixx,num_nil = -1;
		switch (o) {
		// read Ra only
		case OP_SETGLOBAL:
		case OP_SETUPVAL:
			num_nil = a;
			break;
		// read Rb only
		case OP_MOVE:
		case OP_UNM:
		case OP_NOT:
			if (!ISK(b)) {
					num_nil = b;
			}
			break;
		// read Rb and Rc
		case OP_GETTABLE:
		case OP_SETTABLE:
		case OP_SELF:
		case OP_ADD:
		case OP_SUB:
		case OP_MUL:
		case OP_DIV:
		case OP_POW:
		case OP_EQ:
		case OP_LT:
		case OP_LE:
			if (!ISK(b)) {
				num_nil = b;
			}
			if (!ISK(c)) {
				num_nil = MAX(num_nil, c);
			}
			break;
		case OP_RETURN:
			// read Ra to a+b-2
			// only return 1 value
			// move before return multiple values
			num_nil = MAX(num_nil, a+b-2);
			break;
		}
		for (ixx = lastfree; ixx <= num_nil; ixx++) {
			if (ixx!=num_nil) {
				add(locallist,0,last(blocklist));
				lastfree++;
			}
			regassign[lastfree] = 0;
			regusage[lastfree] = 1;
			regblock[lastfree] = last(blocklist);
			lastfree++;
		}
	}
#endif

	// start code checking
	ignoreNext = 0;
	for (pc = 0; pc < f->sizecode; pc++) {
		Instruction instr = f->code[pc];
		OpCode o = GET_OPCODE(instr);
		int a = GETARG_A(instr);
		int b = GETARG_B(instr);
		int c = GETARG_C(instr);
		int bc = GETARG_Bx(instr);
		int sbc = GETARG_sBx(instr);
		// Destination PC for OP_JMPs; it's one greater than the actual dest for some reason. One-indexed?
		int dest = 0;
		// These two are the range of registers modified.
		int setreg = -1;
		int setregto = -1;
		// Unused?
		int setreg2 = -1;
		// These two are the range of registers read.
		int loadreg = -1;
		int loadregto = -1;
		// These two are extra reads.
		int loadreg2 = -1;
		int loadreg3 = -1;
		// These two force a range to be evaluated as possible locals.
		int intlocfrom = -1;
		int intlocto = -1;

		if (ignoreNext) {
			ignoreNext--;
			continue;
		}

		if ((o==OP_JMP)) {
			dest = pc + sbc + 2;
		} else if ((pc+1!=f->sizecode) && (GET_OPCODE(f->code[pc+1])==OP_JMP)) {
			dest = pc + 1 + GETARG_sBx(f->code[pc+1]) + 2;
		}

		// check which registers were read or written to.
		switch (o) {
		case OP_MOVE:
			if (upvaluesToEat > 0) {
				intlocfrom = b;
				intlocto = b;
				break;
			}

			setreg = a;
			if (b<=a) {
				intlocfrom = b;
				intlocto = b;
			}
			loadreg = b;
			break;
		case OP_UNM:
		case OP_NOT:
			setreg = a;
			loadreg = b;
			break;
		case OP_LOADNIL:
			setreg = a;
			setregto = b;
			break;
		case OP_LOADK:
		case OP_GETUPVAL:
		case OP_GETGLOBAL:
		case OP_LOADBOOL:
		case OP_NEWTABLE:
			setreg = a;
			break;
		case OP_GETTABLE:
			setreg = a;
			loadreg = b;
			if (!ISK(c)) {
				loadreg2 = c;
			}
			break;
		case OP_SETGLOBAL:
		case OP_SETUPVAL:
			loadreg = a;
			break;
		case OP_SETTABLE:
			loadreg = a;
			if (!ISK(b)) {
				loadreg2 = b;
			}
			if (!ISK(c)) {
				if (loadreg2==-1) {
					loadreg2 = c;
				} else {
					loadreg3 = c;
				}
				if ((a+1!=c) && (c>a)) {
					intlocto = c-1;
				}
			}
			intlocfrom = 0;
			if (a-1>=intlocto) {
				intlocto = a-1;
			}
			break;
		case OP_ADD:
		case OP_SUB:
		case OP_MUL:
		case OP_DIV:
		case OP_POW:
			setreg = a;
			if (!ISK(b)) {
				loadreg = b;
			}
			if (!ISK(c)) {
				if (loadreg==-1) {
					loadreg = c;
				} else {
					loadreg2 = c;
				}
			}
			break;
		case OP_CONCAT:
			setreg = a;
			loadreg = b;
			loadregto = c;
			break;
		case OP_CALL:
			if (c==0) {
				// Unknown number of return values.
				setreg = a;
				setregto = f->maxstacksize;
			} else if (c>=2) {
				// Set range becomes where the return values are stored.
				setreg = a;
				setregto = a+c-2;
			} else if (c==1) {
				// No return values, intloc range becomes stack start to before the
				// called function.
				intlocfrom = 0;
				intlocto = a-1;
			}
			// b is the number of function arguments + 1
			if (b==0) {
				// "This form is used when the last expression in the parameter
				// list is a function call, so the number of actual parameters is indeterminate"
				loadreg = a;
				loadregto = f->maxstacksize;
			} else {
				// loadreg range becomes the function and all its passed args.
				loadreg = a;
				loadregto = a+b-1;
			}
			break;
		case OP_RETURN:
			if (b==0) {
				loadreg = a;
				loadregto = f->maxstacksize;
			} else if (b>=2) {
				loadreg = a;
				loadregto = a+b-2;
			}
			break;
		case OP_TAILCALL:
			if (b==0) {
				loadreg = a;
				loadregto = f->maxstacksize;
			} else {
				loadreg = a;
				loadregto = a+b-1;
			}
			break;
		case OP_SELF:
			setreg = a;
			setregto = a+1;
			loadreg = b;
			if (a>b) {
				intlocfrom = 0;
				intlocto = b;
			}
			if (!ISK(c)) {
				loadreg2 = c;
			}
			break;
		case OP_EQ:
		case OP_LT:
		case OP_LE:
			if (!ISK(b)) {
				loadreg = b;
			}
			if (!ISK(c)) {
				if (loadreg==-1) {
					loadreg = c;
				} else {
					loadreg2 = c;
				}
			}
			break;
		case OP_TEST:
			if (a == b) {
				// I think this always happens inside an if statement
				loadreg = b;
			}
			else {
				setreg = a;
				loadreg = b;
			}
			break;
		case OP_SETLIST:
			loadreg = a + 1;
			loadregto = a + 1 + bc % LFIELDS_PER_FLUSH;

			break;
		case OP_SETLISTO:
			loadreg = a + 1;
			loadregto = f->maxstacksize;

			break;
		case OP_FORLOOP:
		case OP_TFORLOOP:
			break;
		// TODO: OP_TFORPREP
		//case OP_FORPREP:
		//	loadreg = a;
		//	loadregto = a+2;
		//	setreg = a;
		//	setregto = a+3;
		//	intlocfrom = a;
		//	intlocto = a+3;
		//	regassign[a] = pc;
		//	regassign[a+1] = pc;
		//	regassign[a+2] = pc;
		//	regassign[a+3] = pc+1;
		//	regblock[a] = dest;
		//	regblock[a+1] = dest;
		//	regblock[a+2] = dest;
		//	regblock[a+3] = dest-1;

		//	addi(blocklist, dest-1);
		//	if (GET_OPCODE(f->code[dest-2])==OP_JMP) {
		//		last(blocklist)--;
		//	}
		//	break;
		case OP_JMP:
			//if (GET_OPCODE(f->code[dest-1]) == LUADEC_TFORLOOP) {
			//	int a = GETARG_A(f->code[dest-1]);
			//	int c = GETARG_C(f->code[dest-1]);
			//	setreg = a;
			//	setregto = a+c+2;
			//	loadreg = a;
			//	loadregto = a+2;
			//	intlocfrom = a;
			//	intlocto = a+c+2;
			//	regassign[a] = pc;
			//	regassign[a+1] = pc;
			//	regassign[a+2] = pc;
			//	regblock[a] = dest+1;
			//	regblock[a+1] = dest+1;
			//	regblock[a+2] = dest+1;
			//	for (x=a+3;x<=a+c+2;x++) {
			//		regassign[x] = pc+1;
			//		regblock[x] = dest-1;
			//	}
			//}
			if (dest>pc) {
				addi(blocklist, dest-1);
				// This is true for an if/else statement
				if (GET_OPCODE(f->code[dest-2])==OP_JMP) {
					last(blocklist)--;
				}
			}
			break;
		case OP_CLOSE:
			break;
		case OP_CLOSURE:
			setreg = a;

			++currentClosureIndex;
			Proto* f2 = f->p[currentClosureIndex];
			upvaluesToEat = f2->nups;

			f2->sizeupvalues = f2->nups;
			f2->upvalues = luaM_newvector(luaState, f2->sizeupvalues, TString*);

			break;
		default:
			break;
		}
		
		// Make sure the current list of active blocks is in order (I think?)
		for (i=1; i<blocklist.size; i++) {
			x = blocklist.values[i];
			i2 = i-1;
			while ((i2>=0) && (blocklist.values[i2]<x)) {
				blocklist.values[i2+1] = blocklist.values[i2];
				i2 = i2-1;
			}
			blocklist.values[i2+1] = x;
		}

		if (loadreg!=-1) {
			if (loadregto==-1)
				loadregto = loadreg;
			for (i=loadreg;i<=loadregto;i++) {
				regusage[i]--;
			}
			if (loadreg2!=-1) regusage[loadreg2]--;
			if (loadreg3!=-1) regusage[loadreg3]--;
		}

		if (setreg!=-1) {
			if (setregto==-1)
				setregto = setreg;
			for (i=setreg;i<=setregto;i++) {
				regusage[i]++;
			}
			if (setreg2!=-1) regusage[setreg2]++;
		}

		// i2 becomes the highest register that is probably already a local or will be
		// forced to become one.
		// * Registers ABOVE i2: store start/end block info for use later
		// * Registers BELOW or at i2: add locals
		i2 = lastfree-1;
		for (i=lastfree; i<f->maxstacksize; i++) {
			// * Register loaded from more than once: it's a local being referenced.
			// * Register set to more than once: hard to explain why, but I think
			//    when registers are used that way, it's a local.
			if ((regusage[i]<0) || (regusage[i]>1)) {
				i2 = i;
			}
			// * OP_MOVE: i2 may become as high as the register that's modified.
			// * OP_CALL: If no return values, i2 may become as high as the
			//    register before the function that's called. I'm not sure know why.
			if ((intlocfrom!=-1) && ((intlocfrom<=i) && (i<=intlocto))) {
				i2 = i;
			}
		}

		// Set up the start and end PCs for any new locals. This happens BEFORE
		// the next for loop below, typically in the next instruction.
		for (i=setreg; i<=setregto; i++) {
			if (i>i2) {
				if (blocklist.size == 0) {
					fprintf(stderr, "cannot find blockend, pc = %d, f->sizecode = %d\n", pc, f->sizecode);
				}

				regassign[i] = pc+1;
				regblock[i] = last(blocklist);
			}
		}

		// If the bytecode says to set a register that's greater than lastfree,
		// it means any register before that is a local.
		for (i=lastfree; i<=i2; i++) {
			LocalData local;
			local.startpc = regassign[i];
			local.endpc = regblock[i];
			local.reg = i;
			sprintf(local.name, "l_%d_%d", main, i);
			LocalDataArray_Push(&localList, local);

			lastfree++;
		}

		if (upvaluesToEat > 0 && o != OP_CLOSURE) {
			Proto* f2 = f->p[currentClosureIndex];

			int localIndex = -1;
			for (i = lastfree; i --> 0;) {
				if (localList.values[i].reg == b) {
					localIndex = i;
					break;
				}
			}

			char* name = localList.values[i].name;
			f2->upvalues[f2->nups - upvaluesToEat] = luaS_new(luaState, name);

			--upvaluesToEat;
		}

		// Remove any blocks we exited from the list
		while (blocklist.size > 0 && last(blocklist) <= pc+1) {
			intArray_Pop(&blocklist);
		}

		// Roll back lastfree when we exit a block (aka scope). The locals have
		// already been added, but lastfree is rolled back so we can add more in
		// those register slots.
		while ((lastfree!=0) && (regblock[lastfree-1] <= pc+1)) {
			lastfree--;
			regusage[lastfree]=0;
		}
	}
	intArray_Clear(&blocklist);

	// print out information
	{
		int length = localList.size;
		f->sizelocvars = length;
		if (f->sizelocvars>0) {
			f->locvars = luaM_newvector(luaState,f->sizelocvars,LocVar);
			for (i = 0; i < length; i++) {
				LocalData local = localList.values[i];
				f->locvars[i].varname = luaS_new(luaState, local.name);
				f->locvars[i].startpc = local.startpc;
				f->locvars[i].endpc = local.endpc;
			}
		}
	}
	LocalDataArray_Clear(&localList);

	// run with all functions
	for (i=0; i<f->sizep; i++) {
		luaU_guess_locals(luaState, f->p[i],main+i+1);
	}
	return 1;
}
