#ifndef PREFETCH_INDIRECT
#define PREFETCH_INDIRECT

#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/ADT/ArrayRef.h"
#include <llvm/Support/Debug.h>
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Transforms/Scalar.h"

#include "llvm/Support/raw_ostream.h"

#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#define DEBUG_TYPE "PrefetchIndirect"

using namespace llvm;




// default pass implementation for new Pass manager
struct PrefetchIndirect : PassInfoMixin<PrefetchIndirect> {
     bool makeLoopInvariantSpec(Instruction *I, bool &Changed, Loop* L) const {
      // Test if the value is already loop-invariant.
      if (L->isLoopInvariant(I))
	return true;
      // EH block instructions are immobile.
      // Determine the insertion point, unless one was given.
      if(!I) return false;
      if(!isSafeToSpeculativelyExecute(I) && !I->mayReadFromMemory()) return false; //hacky but it works for now. This is allowed because we're hoisting what are really going to be prefetches.

      BasicBlock *Preheader = L->getLoopPreheader();
      // Without a preheader, hoisting is not feasible.
      if (!Preheader)
	return false;
      Instruction* InsertPt = Preheader->getTerminator();

      // Don't hoist instructions with loop-variant operands.
      for (Value *Operand : I->operands())
	if(Operand) if(Instruction* i = dyn_cast<Instruction>(Operand)) if (!makeLoopInvariantSpec(i, Changed, L)) {
	  Changed = false;
	  return false;
	}

      // Hoist.
      I->moveBefore(InsertPt);

      // There is possibility of hoisting this instruction above some arbitrary
      // condition. Any metadata defined on it can be control dependent on this
      // condition. Conservatively strip it here so that we don't give any wrong
      // information to the optimizer.

      Changed = true;
      return true;
    }

    bool makeLoopInvariantPredecessor(Value *V, bool &Changed, Loop* L) const {
      //if predecessor always runs before the loop, then we can hoist invariant loads, at the expense of exception imprecision.
      //A better technique would retain precision by separating out the first iteration and reusing the invariant loads.



      // Test if the value is already loop-invariant.
      if (L->isLoopInvariant(V))
	return true;

      if(!V) return true;

      Instruction* I = dyn_cast<Instruction>(V);
      if(!I) return false;

      if (!isSafeToSpeculativelyExecute(I) && !I->mayReadFromMemory())
	return false;


      // EH block instructions are immobile.
      if (I->isEHPad())
	return false;

      // Determine the insertion point, unless one was given.

      BasicBlock *Preheader = L->getLoopPreheader();
      // Without a preheader, hoisting is not feasible.
      if (!Preheader)
	return false;
      Instruction* InsertPt = Preheader->getTerminator();


      // Don't hoist instructions with loop-variant operands.
      for (Value *Operand : I->operands())
	if (!makeLoopInvariantPredecessor(Operand, Changed,L))
	  return false;

      // Hoist.
      I->moveBefore(InsertPt);

      // There is possibility of hoisting this instruction above some arbitrary
      // condition. Any metadata defined on it can be control dependent on this
      // condition. Conservatively strip it here so that we don't give any wrong
      // information to the optimizer.
      I->dropUnknownNonDebugMetadata();

      Changed = true;
      return true;
    }

    Value *getArrayOrAllocSize(LoadInst* l, Module *M) const {

      LLVM_DEBUG(dbgs() << "attempting to get size of base array:\n");

      LLVM_DEBUG(l->getPointerOperand()->print(dbgs()));

      GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(l->getPointerOperand());

      if(!gep) {
	LLVM_DEBUG(dbgs() << "Couldn't find gep \n");
	return NULL;
      }

      LLVM_DEBUG(dbgs() << " with ptr: ");
      LLVM_DEBUG(gep->getPointerOperand()->print(dbgs()));


      auto ArrayStart = gep->getPointerOperand();

      if(ArrayType* at = dyn_cast<ArrayType>(gep->getSourceElementType ())) {
	LLVM_DEBUG(dbgs() << " and size: ");
	LLVM_DEBUG(dbgs() << std::to_string(at->getNumElements()));
	int size = at->getNumElements();
	LLVM_DEBUG(dbgs() << "and type: " << *(at->getElementType ()));
	//auto ArrayType = at->getElementType ();



	return  ConstantInt::get(Type::getInt64Ty(M->getContext()),size);

      } else if(AllocaInst* ai = dyn_cast<AllocaInst>(ArrayStart)) {
	LLVM_DEBUG(dbgs() << "and dynamic allocated size " << *(ai->getArraySize()));
	LLVM_DEBUG(dbgs() << *(ai->getArraySize ()));
	//dbgs() << *(gep->getSourceElementType ());
	//SequentialType* pt = dyn_cast<SequentialType>(gep->getSourceElementType ());
	LLVM_DEBUG(dbgs() << "and type: ");
	LLVM_DEBUG(dbgs() << *(gep->getSourceElementType ()));//*(pt->getElementType ());
	//p->ArrayType = (gep->getSourceElementType ());


	//  ConstantInt::get(Type::getInt64Ty(Mod.getContext()),0),
	// ConstantInt::get(Type::getInt64Ty(Mod.getContext()),0),
	return   ai->getArraySize ();


      }

      return NULL;





    }

    Value *getCanonicalishSizeVariable(Loop* L) const {

      // Loop over all of the PHI nodes, looking for a canonical indvar.


      auto B = L->getExitingBlock();

      if(!B) return nullptr;

      CmpInst *CI = nullptr;

      //really, should be reverse dataflow from the terminating jump
      for(Instruction &J : *B) {

	Instruction* I = &J;
	CI = dyn_cast<CmpInst>(I) ? dyn_cast<CmpInst>(I) : CI;

      }
      bool Changed = false;

      if(CI) {
	if(L->makeLoopInvariant(CI->getOperand(1),Changed) || makeLoopInvariantPredecessor(CI->getOperand(1),Changed,L)) return CI->getOperand(1);

	if(L->makeLoopInvariant(CI->getOperand(0),Changed) || makeLoopInvariantPredecessor(CI->getOperand(1),Changed,L)) return CI->getOperand(0);

	LLVM_DEBUG(dbgs() << "Size not loop invariant!" << *(CI->getOperand(0)) << *(CI->getOperand(1)) << "\n");

	//return nullptr;
      }






      return nullptr;
    }

    PHINode *getCanonicalishInductionVariable(Loop* L) const {
      BasicBlock *H = L->getHeader();

      BasicBlock *Incoming = nullptr, *Backedge = nullptr;
      pred_iterator PI = pred_begin(H);
      assert(PI != pred_end(H) &&
	  "Loop must have at least one backedge!");
      Backedge = *PI++;
      if (PI == pred_end(H)) return nullptr;  // dead loop
      Incoming = *PI++;
      if (PI != pred_end(H)) return nullptr;  // multiple backedges?

      if (L->contains(Incoming)) {
	if (L->contains(Backedge))
	  return nullptr;
	std::swap(Incoming, Backedge);
      } else if (!L->contains(Backedge))
	return nullptr;


      // Loop over all of the PHI nodes, looking for a canonical indvar.
      for (BasicBlock::iterator I = H->begin(); isa<PHINode>(I); ++I) {
	PHINode *PN = cast<PHINode>(I);
	if(!PN->getIncomingValueForBlock(Backedge)) return nullptr;
	if (Instruction *Inc =
	    dyn_cast<Instruction>(PN->getIncomingValueForBlock(Backedge)))
	  if (Inc->getOpcode() == Instruction::Add &&
	      Inc->getOperand(0) == PN)
	    if (dyn_cast<ConstantInt>(Inc->getOperand(1)))
	      return PN;
      }
      return nullptr;
    }


    PHINode *getWeirdCanonicalishInductionVariable(Loop* L) const {
      BasicBlock *H = L->getHeader();

      BasicBlock *Incoming = nullptr, *Backedge = nullptr;
      pred_iterator PI = pred_begin(H);
      assert(PI != pred_end(H) &&
	  "Loop must have at least one backedge!");
      Backedge = *PI++;
      if (PI == pred_end(H)) return nullptr;  // dead loop
      Incoming = *PI++;
      if (PI != pred_end(H)) return nullptr;  // multiple backedges?

      if (L->contains(Incoming)) {
	if (L->contains(Backedge))
	  return nullptr;
	std::swap(Incoming, Backedge);
      } else if (!L->contains(Backedge))
	return nullptr;

      // Loop over all of the PHI nodes, looking for a canonical indvar.
      for (BasicBlock::iterator I = H->begin(); isa<PHINode>(I); ++I) {
	PHINode *PN = cast<PHINode>(I);
	if (GetElementPtrInst *Inc =
	    dyn_cast<GetElementPtrInst>(PN->getIncomingValueForBlock(Backedge)))
	  if (Inc->getOperand(0) == PN)
	    if (ConstantInt *CI = dyn_cast<ConstantInt>(Inc->getOperand(Inc->getNumOperands()-1)))
	      if (CI->equalsInt(1))
		return PN;
      }
      return nullptr;
    }


    GetElementPtrInst *getWeirdCanonicalishInductionVariableGep(Loop* L) const {
      BasicBlock *H = L->getHeader();

      BasicBlock *Incoming = nullptr, *Backedge = nullptr;
      pred_iterator PI = pred_begin(H);
      assert(PI != pred_end(H) &&
	  "Loop must have at least one backedge!");
      Backedge = *PI++;
      if (PI == pred_end(H)) return nullptr;  // dead loop
      Incoming = *PI++;
      if (PI != pred_end(H)) return nullptr;  // multiple backedges?

      if (L->contains(Incoming)) {
	if (L->contains(Backedge))
	  return nullptr;
	std::swap(Incoming, Backedge);
      } else if (!L->contains(Backedge))
	return nullptr;

      // Loop over all of the PHI nodes, looking for a canonical indvar.
      for (BasicBlock::iterator I = H->begin(); isa<PHINode>(I); ++I) {
	PHINode *PN = cast<PHINode>(I);
	if (GetElementPtrInst *Inc =
	    dyn_cast<GetElementPtrInst>(PN->getIncomingValueForBlock(Backedge)))
	  if (Inc->getOperand(0) == PN)
	    if (ConstantInt *CI = dyn_cast<ConstantInt>(Inc->getOperand(Inc->getNumOperands()-1)))
	      if (CI->equalsInt(1))
		return Inc;
      }
      return nullptr;
    }


    Value *getWeirdCanonicalishInductionVariableFirst(Loop* L) const {
      BasicBlock *H = L->getHeader();

      BasicBlock *Incoming = nullptr, *Backedge = nullptr;
      pred_iterator PI = pred_begin(H);
      assert(PI != pred_end(H) &&
	  "Loop must have at least one backedge!");
      Backedge = *PI++;
      if (PI == pred_end(H)) return nullptr;  // dead loop
      Incoming = *PI++;
      if (PI != pred_end(H)) return nullptr;  // multiple backedges?

      if (L->contains(Incoming)) {
	if (L->contains(Backedge))
	  return nullptr;
	std::swap(Incoming, Backedge);
      } else if (!L->contains(Backedge))
	return nullptr;

      // Loop over all of the PHI nodes, looking for a canonical indvar.
      for (BasicBlock::iterator I = H->begin(); isa<PHINode>(I); ++I) {
	PHINode *PN = cast<PHINode>(I);
	if (GetElementPtrInst *Inc =
	    dyn_cast<GetElementPtrInst>(PN->getIncomingValueForBlock(Backedge)))
	  if (Inc->getOperand(0) == PN)
	    if (ConstantInt *CI = dyn_cast<ConstantInt>(Inc->getOperand(Inc->getNumOperands()-1)))
	      if (CI->equalsInt(1))
		return PN->getIncomingValueForBlock(Incoming);
      }
      return nullptr;
    }

    Value *getOddPhiFirst(Loop* L, PHINode* PN) const {
      BasicBlock *H = L->getHeader();

      BasicBlock *Incoming = nullptr, *Backedge = nullptr;
      pred_iterator PI = pred_begin(H);
      assert(PI != pred_end(H) &&
	  "Loop must have at least one backedge!");
      Backedge = *PI++;
      if (PI == pred_end(H)) return nullptr;  // dead loop
      Incoming = *PI++;
      if (PI != pred_end(H)) return nullptr;  // multiple backedges?

      if(H != PN->getParent()) return nullptr;

      if (L->contains(Incoming)) {
	if (L->contains(Backedge))
	  return nullptr;
	std::swap(Incoming, Backedge);
      } else if (!L->contains(Backedge))
	return nullptr;

      return PN->getIncomingValueForBlock(Incoming);

    }




    bool depthFirstSearch (Instruction* I, LoopInfo &LI, Instruction* &Phi, SmallVector<Instruction*,8> &Instrs, SmallVector<Instruction*,4> &Loads, SmallVector<Instruction*,4> &Phis, std::vector<SmallVector<Instruction*,8>>& Insts) {
      Use* u = I->getOperandList();
      Use* end = u + I->getNumOperands();

      SetVector<Instruction*> roundInsts;

      bool found = false;

      for(Use* v = u; v<end; v++) {

	PHINode* p = dyn_cast<PHINode>(v->get());
	Loop* L = nullptr;
	if(p) L = LI.getLoopFor(p->getParent());

	if(p && L && (p == getCanonicalishInductionVariable (L) || p == getWeirdCanonicalishInductionVariable(L))) {



	  LLVM_DEBUG(dbgs() << "Loop induction phi node! " << *p << "\n");

	  if(Phi) {
	    if(Phi == p) {
	      //add this
	      roundInsts.remove(p);
	      roundInsts.insert (p);
	      found = true; //should have been before anyway
	    } else {
	      //check which is older.
	      if(LI.getLoopFor(Phi->getParent())->isLoopInvariant(p)) {
		//do nothing
		LLVM_DEBUG(dbgs() << "not switching phis\n");
	      } else if (LI.getLoopFor(p->getParent())->isLoopInvariant(Phi)) {
		LLVM_DEBUG(dbgs() << "switching phis\n");
		roundInsts.clear();
		roundInsts.insert (p);
		Phi = p;
		found = true;
	      } else {
		assert(0);
	      }
	    }
	  } else {

	    Phi = p;
	    roundInsts.remove(p);
	    roundInsts.insert (p);
	    found = true;
	  }



	}
	else if(dyn_cast<StoreInst>(v->get())) {}
	else if(dyn_cast<CallInst>(v->get())) {}
	else if(dyn_cast<Instruction>(v->get()) && dyn_cast<Instruction>(v->get())->isTerminator()) {}
	else if(LoadInst * linst = dyn_cast<LoadInst>(v->get())) {
	  //Cache results

	  int lindex=-1;
	  int index=0;
	  for( auto l: Loads) {
	    if (l == linst) {
	      lindex=index;
	      break;
	    }
	    index++;
	  }

	  if(lindex!=-1) {
	    Instruction* phi = Phis[lindex];

	    if(Phi) {
	      if(Phi == phi) {
		//add this
		for(auto q : Insts[lindex]) {
		  roundInsts.remove(q);
		  roundInsts.insert (q);
		}
		found = true; //should have been before anyway
	      } else {
		//check which is older.
		if(LI.getLoopFor(Phi->getParent())->isLoopInvariant(phi)) {
		  //do nothing
		  LLVM_DEBUG(dbgs() << "not switching phis\n");
		} else if (LI.getLoopFor(phi->getParent())->isLoopInvariant(Phi)) {
		  LLVM_DEBUG(dbgs() << "switching phis\n");
		  roundInsts.clear();
		  for(auto q : Insts[lindex]) {
		    roundInsts.remove(q);
		    roundInsts.insert (q);
		  }
		  Phi = phi;
		  found = true;
		} else {
		  assert(0);
		}
	      }
	    } else {
	      for(auto q : Insts[lindex]) {
		roundInsts.remove(q);
		roundInsts.insert (q);
	      }
	      Phi = phi;
	      found = true;
	    }

	  }



	}
	else if(v->get()) if(Instruction* k = dyn_cast<Instruction>(v->get())) {

	  if(!((!p) || L != nullptr)) continue;

	  Instruction* j = k;

	  Loop* L = LI.getLoopFor(j->getParent());
	  if(L) {

	    SmallVector<Instruction*,8> Instrz;



	    if(p) {
	      LLVM_DEBUG(dbgs() << "Non-loop-induction phi node! " << *p << "\n");
	      j = nullptr;
	      if(!getOddPhiFirst(L,p)) {
		return false;
	      }
	      j = dyn_cast<Instruction> (getOddPhiFirst(L,p));
	      if(!j) {
		return false;
	      }
	      Instrz.push_back(k);
	      Instrz.push_back(j);
	      L = LI.getLoopFor(j->getParent());

	    } else Instrz.push_back(k);




	    Instruction * phi = nullptr;
	    if(depthFirstSearch(j,LI,phi, Instrz, Loads, Phis, Insts)) {
	      if(Phi) {
		if(Phi == phi) {
		  //add this
		  for(auto q : Instrz) {
		    roundInsts.remove(q);
		    roundInsts.insert (q);
		  }
		  found = true; //should have been before anyway
		} else {
		  //check which is older.
		  if(LI.getLoopFor(Phi->getParent())->isLoopInvariant(phi)) {
		    //do nothing
		    LLVM_DEBUG(dbgs() << "not switching phis\n");
		  } else if (LI.getLoopFor(phi->getParent())->isLoopInvariant(Phi)) {
		    LLVM_DEBUG(dbgs() << "switching phis\n");
		    roundInsts.clear();
		    for(auto q : Instrz) {
		      roundInsts.remove(q);
		      roundInsts.insert (q);
		    }
		    Phi = phi;
		    found = true;
		  } else {
		    assert(0);
		  }
		}
	      } else {
		for(auto q : Instrz) {
		  roundInsts.remove(q);
		  roundInsts.insert (q);
		}
		Phi = phi;
		found = true;
	      }
	    }
	  }
	}
      }


      if(found) for(auto q : roundInsts) Instrs.push_back(q);

      return found;
    }

    PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM);
    
};

#endif //PREFETCH_INDIRECT