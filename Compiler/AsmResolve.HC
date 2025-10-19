U0 AOTLocalsResolve(CCmpCtrl *cc)
{
  if (!cc || !cc->aotc) return; //safety

  CAOTCtrl *aotc=cc->aotc;
  CAsmUnresolvedRef *tmpu=aotc->local_unresolved,*tmpu1;
  CAsmUndefHash *tmpauh;
  Bool undefined;
  U8 *label=NULL;

  while (tmpu) {
    undefined=FALSE;
    tmpu1=tmpu->next;
    tmpauh=tmpu->asm_undef_hash;

    while (tmpauh) {
      if (tmpauh->hash) {
        if (tmpauh->hash->type & HTF_UNRESOLVED) {
	  PrintErr("Undefined sym at line:%04d %s %s\n",
	           tmpu->line_num, aotc->last_label, tmpauh->hash->str);
	  LexExcept(cc);
        }
	label=tmpauh->hash->str;
      }
      tmpauh=tmpauh->next;
    }

    if (!undefined)
      AsmResolve(cc,tmpu,label,FALSE);

    if (tmpu->machine_code) Free(tmpu->machine_code);
    LinkedLstDel(tmpu->asm_undef_hash);
    Free(tmpu);
    tmpu=tmpu1;
  }

  if (cc->htc.local_hash_table) HashTableDel(cc->htc.local_hash_table);
  cc->htc.hash_table_lst = cc->htc.local_hash_table = HashTableNew(16);
  cc->htc.local_hash_table->next = cc->htc.glbl_hash_table;
  aotc->local_unresolved = NULL;
}


U0 AOTGlblsResolve(CCmpCtrl *cc, CAOT *tmpaot)
{
  if (!cc || !cc->aotc || !tmpaot) return; //safety

  CAOTCtrl *aotc=cc->aotc;
  CAsmUnresolvedRef *tmpu=aotc->glbl_unresolved,*tmpu1;
  CAsmUndefHash *tmpauh;
  CHashExport *tmpex;
  CHashFun *tmpf;
  CAOTImportExport *tmpie,*tmpie1;
  CExternUsage *tmpeu,*tmpeu8;
  U8 *label;
  Bool undefined;
  I64 i,j;

  while (tmpu) {
    label=NULL;
    undefined=FALSE;
    tmpu1=tmpu->next;
    tmpauh=tmpu->asm_undef_hash;

    while (tmpauh) {
      if (tmpauh->hash) {
	if (tmpauh->hash->type & HTF_UNRESOLVED) {
	  tmpex = tmpauh->hash;
	  if ((tmpex->type & HTT_EXPORT_SYS_SYM) && 
	      (tmpex->type & HTF_UNRESOLVED) &&
	      !(tmpex->type & HTF_IMPORT) &&
	      (tmpf = HashFind(tmpex->str, cc->htc.hash_table_lst, HTT_FUN)) &&
	      !Bt(&tmpf->flags,Cf_EXTERN)) {
	    tmpex->val = tmpf->exe_addr;
	    tmpex->type &= ~HTF_UNRESOLVED;
	    label = tmpauh->hash->str;
	  } else {
	    if (!(tmpex->type & HTF_IMPORT)) {
	      if (cc->htc.local_var_lst) {
		tmpex->type |= HTF_GOTO_LABEL;
		tmpex->use_cnt++;
	      } else {
		PrintErr("Undefined sym at line:%04d %s\n", tmpu->line_num, tmpex->str);
		LexExcept(cc);
	      }
	    } else if (undefined) {
	      PrintErr("Two imports in same expression not allowed at line:%04d %s\n",
	               tmpu->line_num, tmpex->str);
	      LexExcept(cc);
	    }
	    undefined = TRUE;
	  }
	} else
	  label = tmpauh->hash->str;
      }
      tmpauh = tmpauh->next;
    }

    AsmResolve(cc, tmpu, label, undefined);
    if (tmpu->machine_code) Free(tmpu->machine_code);
    LinkedLstDel(tmpu->asm_undef_hash);
    Free(tmpu);
    tmpu = tmpu1;
  }

  //resolve global exports
  for (i=0;i<=cc->htc.glbl_hash_table->mask;i++) {
    tmpex = cc->htc.glbl_hash_table->body[i];
    while (tmpex) {
      if (tmpex->type & (HTF_IMPORT|HTF_GOTO_LABEL)) {
	if (tmpex->use_cnt && (tmpie = tmpex->ie_lst)) {
	  if (tmpex->type & HTF_GOTO_LABEL)
	    tmpie->flags |= IEF_GOTO_LABEL;
	  if (tmpex->import_name)
	    tmpie->str = StrNew(tmpex->import_name);
	  else
	    tmpie->str = StrNew(tmpex->str);

	  do {
	    tmpie1 = tmpie->next;
	    QueIns(tmpie, tmpaot->last_ie);
	  } while (tmpie = tmpie1);

	  tmpex->ie_lst = NULL;
	}
      } else if (tmpex->type & (HTF_EXPORT|HTF_RESOLVE)) {
	if (tmpex->type & HTF_UNRESOLVED) {
	  PrintErr("Undefined sym at %s\n", tmpex->str);
	  LexExcept(cc);
	}

	if (tmpex->type & HTF_RESOLVE) {
	  tmpf = tmpex;
	  tmpeu = tmpf->ext_lst;
	  while (tmpeu) {
	    tmpeu8 = tmpeu->next;
	    j = tmpf->exe_addr - (tmpeu->rip+4);
	    //store safely
	    AOTStoreCodeU8At(cc, tmpeu->rip, j.u8[0], j.u8[1], j.u8[2], j.u8[3]);
	    Free(tmpeu);
	    tmpeu = tmpeu8;
	  }
	}

	if (tmpex->type & HTF_EXPORT) {
	  tmpie = CAlloc(sizeof(CAOTImportExport));
	  if (!tmpie) { PrintErr("OOM allocating CAOTImportExport\n"); return; }
	  tmpie->type = IET_REL32_EXPORT;
	  if (tmpex->type & HTT_FUN)
	    tmpie->rip = tmpf->exe_addr;
	  else if (tmpex->type & HTT_GLBL_VAR)
	    tmpie->rip = tmpex(CHashGlblVar *)->data_addr_rip;
	  else
	    tmpie->rip = tmpex->val;
	  tmpie->aot = cc->aot;
	  if (tmpex->type & HTF_IMM)
	    tmpie->type++;
	  tmpie->str = StrNew(tmpex->str);
	  tmpie->src_link = StrNew(tmpex->src_link);
	  QueIns(tmpie, tmpaot->last_ie);
	}
      }
      tmpex = tmpex->next;
    }
  }
}


U0 AsmUnresolvedAdd(CCmpCtrl *cc,U8 *machine_code,I64 type,I64 rip,I64 rel_rip,
	CAsmUndefHash *local_asm_undef_hash,CAsmUndefHash *glbl_asm_undef_hash,
	I64 line_num,Bool U8_avail)
{
  if (!cc) return; //safety

  CAsmUnresolvedRef *tmpu = MAlloc(sizeof(CAsmUnresolvedRef));
  if (!tmpu) { PrintErr("OOM allocating CAsmUnresolvedRef\n"); return; }

  tmpu->machine_code = machine_code;
  tmpu->type = type;
  tmpu->rip = rip;
  tmpu->rel_rip = rel_rip;
  tmpu->aot = cc->aot;
  tmpu->imm_flag = FALSE;
  tmpu->line_num = line_num;
  tmpu->U8_avail = U8_avail;
  tmpu->str = NULL;

  if (local_asm_undef_hash) {
    tmpu->asm_undef_hash = local_asm_undef_hash;
    tmpu->next = cc->aotc->local_unresolved;
    cc->aotc->local_unresolved = tmpu;
  } else {
    tmpu->asm_undef_hash = glbl_asm_undef_hash;
    tmpu->next = cc->aotc->glbl_unresolved;
    cc->aotc->glbl_unresolved = tmpu;
    if (glbl_asm_undef_hash && glbl_asm_undef_hash->hash &&
        (glbl_asm_undef_hash->hash->type & HTF_IMPORT)) {
      tmpu->str = StrNew(glbl_asm_undef_hash->hash->str);
      if (glbl_asm_undef_hash->hash->type & HTF_IMM)
	tmpu->imm_flag = TRUE;
    }
  }
}
