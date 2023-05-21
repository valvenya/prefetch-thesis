//=============================================================================
//    1. Legacy PM
//      opt -load libHelloWorld.dylib -legacy-hello-world -disable-output `\`
//        <input-llvm-file>
//    2. New PM
//      opt -load-pass-plugin=libHelloWorld.dylib -passes="hello-world" `\`
//        -disable-output <input-llvm-file>
//=============================================================================


#include "PrefetchIndirect.h"


#ifdef NO_STRIDES
#define C_CONSTANT (32)
#else
#define C_CONSTANT (64)
#endif

#ifndef IGNORE_SIZE
#define IGNORE_SIZE 0
#endif

/// New PM implementation
PreservedAnalyses PrefetchIndirect::run(Function &F, FunctionAnalysisManager &FAM) {
    LoopInfo &LI = FAM.getResult<LoopAnalysis>(F);
    Module *M = F.getParent();

    bool modified = false;

    SmallVector<Instruction*,4> Loads;
    SmallVector<Instruction*,4> Phis;
    SmallVector<int,4> Offsets;
    SmallVector<int,4> MaxOffsets;
    std::vector<SmallVector<Instruction*,8>> Insts;

    for(auto &BB : F) {
    for (auto &I : BB) {
        if (LoadInst *i = dyn_cast<LoadInst>(&I)) {
        if(LI.getLoopFor(&BB)) {
            SmallVector<Instruction*,8> Instrz;
            Instrz.push_back(i);
            Instruction * phi = nullptr;
            if(depthFirstSearch(i,LI,phi,Instrz,  Loads, Phis, Insts)) {

        int loads = 0;
        for(auto &z : Instrz) {
            if(dyn_cast<LoadInst>(z)) {
            loads++;
            }
        }

        if(loads < 2) {
            LLVM_DEBUG(dbgs()<<"stride\n");    //don't remove the stride cases yet though. Only remove them once we know it's not in a sequence with an indirect.
    #ifdef NO_STRIDES
            //add a continue in here to avoid generating strided prefetches. Make sure to reduce the value of C accordingly!
            continue;
    #endif
        }

        LLVM_DEBUG(dbgs() << "Can prefetch " << *i << " from PhiNode " << *phi << "\n");
        LLVM_DEBUG(dbgs() << "need to change \n");
        for (auto &z : Instrz) {
            LLVM_DEBUG(dbgs() << *z << "\n");
        }

        Loads.push_back(i);
        Insts.push_back(Instrz);
        Phis.push_back(phi);
        Offsets.push_back(0);
        MaxOffsets.push_back(1);

            }
            else {
        LLVM_DEBUG(dbgs() << "Can't prefetch load" << *i << "\n");
            }

        }
        }
    }


        }

        for(uint64_t x=0; x<Loads.size(); x++) {
    ValueMap<Instruction*, Value*> Transforms;

    bool ignore = true;

    Loop* L = LI.getLoopFor(Phis[x]->getParent());


    for(uint64_t y=x+1; y< Loads.size(); y++) {
        bool subset = true;
        for(auto &in : Insts[x]) {
        if(std::find(Insts[y].begin(),Insts[y].end(),in) == Insts[y].end()) subset = false;
        }
        if(subset) {
        MaxOffsets[x]++;
        Offsets[y]++;
        ignore=false;
        }
    }

    int loads = 0;

    LoadInst* firstLoad = NULL;

    for(auto &z : Insts[x]) {
        if(dyn_cast<LoadInst>(z)) {
        if(!firstLoad) firstLoad = dyn_cast<LoadInst>(z);
        loads++;
        }
    }


    //loads limited to two on second case, to avoid needing to check bound validity on later loads.
    if((getCanonicalishSizeVariable(L)) == nullptr) {
        if(!getArrayOrAllocSize(firstLoad, M) || loads >2)
        continue;

    }

    if(loads < 2 && ignore) {
        LLVM_DEBUG(dbgs() << "Ignoring" << *(Loads[x]) << "\n");
        continue; //remove strides with no dependent indirects.
    }


    IRBuilder<> Builder(Loads[x]);

    bool tryToPushDown = (LI.getLoopFor(Loads[x]->getParent()) != LI.getLoopFor(Phis[x]->getParent()));

    if(tryToPushDown) LLVM_DEBUG(dbgs() << "Trying to push down!\n");



    //reverse list.
    SmallVector<Instruction*,8> newInsts;
    for(auto q = Insts[x].end()-1; q > Insts[x].begin()-1; q--) newInsts.push_back(*q);
    for(auto &z : newInsts) {
        if(Transforms.count(z)) continue;



        if(z == Phis[x]) {

        Instruction* n;

        bool weird = false;

        Loop* L = LI.getLoopFor(Phis[x]->getParent());

        int offset = (C_CONSTANT*MaxOffsets[x])/(MaxOffsets[x]+Offsets[x]);

        if(z == getCanonicalishInductionVariable(L)) {
            n = dyn_cast<Instruction>(Builder.CreateAdd(Phis[x],Phis[x]->getType()->isIntegerTy(64) ? ConstantInt::get(Type::getInt64Ty(M->getContext()),offset) : ConstantInt::get(Type::getInt32Ty(M->getContext()),offset)));
    #ifdef BROKEN


            n = dyn_cast<Instruction>(Builder.CreateAnd(n,1));


    #endif
        }
        else if (z == getWeirdCanonicalishInductionVariable(L)) {
            //This covers code where a pointer is incremented, instead of a canonical induction variable.

            n = getWeirdCanonicalishInductionVariableGep(L)->clone();
            Builder.Insert(n);
            n->setOperand (n->getNumOperands ()-1, ConstantInt::get(Type::getInt64Ty(M->getContext()),offset));
            weird = true;

            bool changed = true;
            while(LI.getLoopFor(Phis[x]->getParent()) != LI.getLoopFor(n->getParent()) && changed) {

        Loop* ol = LI.getLoopFor(n->getParent());

        makeLoopInvariantSpec(n,changed,LI.getLoopFor(n->getParent()));

        if(ol && ol == LI.getLoopFor(n->getParent())) break;


            }

        }




        assert(L);
        assert(n);

        Value* size = getCanonicalishSizeVariable(L);
        if(!size) {
            size = getArrayOrAllocSize(firstLoad, M);
        }
        assert(size);
        std::string type_str;
        llvm::raw_string_ostream rso(type_str);
        size->getType()->print(rso);
        rso.flush();
        /* assert(size->getType()->isIntegerTy() || IGNORE_SIZE); */
        if(loads< 2 || !size || !size->getType()->isIntegerTy() || IGNORE_SIZE) {
            Transforms.insert(std::pair<Instruction*,Instruction*>(z,n));
            continue;
        }


        Instruction* mod;

        if(weird) {
            //This covers code where a pointer is incremented, instead of a canonical induction variable.

            Instruction* endcast = dyn_cast<Instruction>(Builder.CreatePtrToInt(size,Type::getInt64Ty(M->getContext())));


            Instruction* startcast =  dyn_cast<Instruction>(Builder.CreatePtrToInt(getWeirdCanonicalishInductionVariableFirst(L),Type::getInt64Ty(M->getContext())));


            Instruction* valcast =  dyn_cast<Instruction>(Builder.CreatePtrToInt(n,Type::getInt64Ty(M->getContext())));


            Instruction* sub1 = dyn_cast<Instruction>(Builder.CreateSub(valcast,startcast));
            Instruction* sub2 = dyn_cast<Instruction>(Builder.CreateSub(endcast,startcast));

            Value* cmp = Builder.CreateICmp(CmpInst::ICMP_SLT,sub1,sub2);
            Instruction* rem = dyn_cast<Instruction>(Builder.CreateSelect(cmp,sub1,sub2));

            Instruction* add = dyn_cast<Instruction>(Builder.CreateAdd(rem,startcast));

            mod = dyn_cast<Instruction>(Builder.CreateIntToPtr(add,n->getType()));






        }
        else if(size->getType() != n->getType()) {
            Instruction* cast = CastInst::CreateIntegerCast(size,n->getType(),true);
            assert(cast);
            Builder.Insert(cast);
            Value* sub = Builder.CreateSub(cast,ConstantInt::get(Type::getInt64Ty(M->getContext()),1));
            Value* cmp = Builder.CreateICmp(CmpInst::ICMP_SLT,sub,n);
            mod = dyn_cast<Instruction>(Builder.CreateSelect(cmp,sub,n));

        } else {

            Value* sub = Builder.CreateSub(size,ConstantInt::get(n->getType(),1));
            Value* cmp = Builder.CreateICmp(CmpInst::ICMP_SLT,sub,n);
            mod = dyn_cast<Instruction>(Builder.CreateSelect(cmp,sub,n));
        }


        bool changed = true;
        while(LI.getLoopFor(Phis[x]->getParent()) != LI.getLoopFor(mod->getParent()) && changed) {
            Loop* ol = LI.getLoopFor(mod->getParent());
            makeLoopInvariantSpec(mod,changed,LI.getLoopFor(mod->getParent()));
            if(ol && ol == LI.getLoopFor(mod->getParent())) break;
        }

        Transforms.insert(std::pair<Instruction*,Instruction*>(z,mod));
        modified = true;
        } else if (z == Loads[x]) {
        assert(Loads[x]->getOperand(0));

        Instruction* oldGep = dyn_cast<Instruction>(Loads[x]->getOperand(0));
        assert(oldGep);

        assert(Transforms.lookup(oldGep));
        Instruction* gep = dyn_cast<Instruction>(Transforms.lookup(oldGep));
        assert(gep);
        modified = true;


        Instruction* cast = dyn_cast<Instruction>(Builder.CreateBitCast (gep, Type::getInt8PtrTy(M->getContext())));


        bool changed = true;
        while(LI.getLoopFor(Phis[x]->getParent()) != LI.getLoopFor(cast->getParent()) && changed) {
            Loop* ol = LI.getLoopFor(cast->getParent());
            makeLoopInvariantSpec(cast,changed,ol);
            if(ol && ol == LI.getLoopFor(cast->getParent())) break;
        }


        Value* ar[] = {
            cast,
            ConstantInt::get(Type::getInt32Ty(M->getContext()),0),
            ConstantInt::get(Type::getInt32Ty(M->getContext()),3),
            ConstantInt::get(Type::getInt32Ty(M->getContext()),1)
        };
        ArrayRef<Type *> art = {
            Type::getInt8PtrTy(M->getContext())
        };
        Function *fun = Intrinsic::getDeclaration(M, Intrinsic::prefetch, art);

        assert(fun);

        CallInst* call = CallInst::Create(fun,ar);

        call->insertBefore(cast->getParent()->getTerminator());





        } else if(PHINode * pn = dyn_cast<PHINode>(z)) {

        Value* v = getOddPhiFirst(LI.getLoopFor(pn->getParent()),pn);
        //assert(v);
        if(v) {
            if(Instruction* ins = dyn_cast<Instruction>(v)) v = Transforms.lookup(ins);
            Transforms.insert(std::pair<Instruction*,Value*>(z,v));
        } else {
            Transforms.insert(std::pair<Instruction*,Value*>(z,z));
        }
        }
        else {

        Instruction* n = z->clone();

        Use* u = n->getOperandList();
        int64_t size = n->getNumOperands();
        for(int64_t x = 0; x<size; x++) {
            Value* v = u[x].get();
            assert(v);
            if(Instruction* t = dyn_cast<Instruction>(v)) {
        if(Transforms.count(t)) {
            n->setOperand(x,Transforms.lookup(t));
        }
            }
        }

        n->insertBefore(Loads[x]);

        bool changed = true;
        while(changed && LI.getLoopFor(Phis[x]->getParent()) != LI.getLoopFor(n->getParent())) {
            changed = false;

            makeLoopInvariantSpec(n,changed,LI.getLoopFor(n->getParent()));
            if(changed) LLVM_DEBUG(dbgs()<< "moved loop" << *n << "\n");
            else LLVM_DEBUG(dbgs()<< "not moved loop" << *n << "\n");

        }

        Transforms.insert(std::pair<Instruction*,Instruction*>(z,n));
        modified = true;
        }

    }


        }
    if (modified)
        return PreservedAnalyses::none();
    
    return PreservedAnalyses::all();
}