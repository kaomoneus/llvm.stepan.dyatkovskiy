def addrimm12 : ComplexPattern<iPTR, 2, "selectIntAddrMM", [frameindex]>;

def simm12 : Operand<i32> {
  let DecoderMethod = "DecodeSimm12";
}

def mem_mm_12 : Operand<i32> {
  let PrintMethod = "printMemOperand";
  let MIOperandInfo = (ops GPR32, simm12);
  let EncoderMethod = "getMemEncodingMMImm12";
  let ParserMatchClass = MipsMemAsmOperand;
  let OperandType = "OPERAND_MEMORY";
}

let canFoldAsLoad = 1 in
class LoadLeftRightMM<string opstr, SDNode OpNode, RegisterOperand RO,
                      Operand MemOpnd> :
  InstSE<(outs RO:$rt), (ins MemOpnd:$addr, RO:$src),
         !strconcat(opstr, "\t$rt, $addr"),
         [(set RO:$rt, (OpNode addrimm12:$addr, RO:$src))],
         NoItinerary, FrmI> {
  let DecoderMethod = "DecodeMemMMImm12";
  string Constraints = "$src = $rt";
}

class StoreLeftRightMM<string opstr, SDNode OpNode, RegisterOperand RO,
                       Operand MemOpnd>:
  InstSE<(outs), (ins RO:$rt, MemOpnd:$addr),
         !strconcat(opstr, "\t$rt, $addr"),
         [(OpNode RO:$rt, addrimm12:$addr)], NoItinerary, FrmI> {
  let DecoderMethod = "DecodeMemMMImm12";
}

let DecoderNamespace = "MicroMips", Predicates = [InMicroMips] in {
  /// Arithmetic Instructions (ALU Immediate)
  def ADDiu_MM : MMRel, ArithLogicI<"addiu", simm16, GPR32Opnd>,
                 ADDI_FM_MM<0xc>;
  def ADDi_MM  : MMRel, ArithLogicI<"addi", simm16, GPR32Opnd>,
                 ADDI_FM_MM<0x4>;
  def SLTi_MM  : MMRel, SetCC_I<"slti", setlt, simm16, immSExt16, GPR32Opnd>,
                 SLTI_FM_MM<0x24>;
  def SLTiu_MM : MMRel, SetCC_I<"sltiu", setult, simm16, immSExt16, GPR32Opnd>,
                 SLTI_FM_MM<0x2c>;
  def ANDi_MM  : MMRel, ArithLogicI<"andi", uimm16, GPR32Opnd>,
                 ADDI_FM_MM<0x34>;
  def ORi_MM   : MMRel, ArithLogicI<"ori", uimm16, GPR32Opnd>,
                 ADDI_FM_MM<0x14>;
  def XORi_MM  : MMRel, ArithLogicI<"xori", uimm16, GPR32Opnd>,
                 ADDI_FM_MM<0x1c>;
  def LUi_MM   : MMRel, LoadUpper<"lui", GPR32Opnd, uimm16>, LUI_FM_MM;

  /// Arithmetic Instructions (3-Operand, R-Type)
  def ADDu_MM  : MMRel, ArithLogicR<"addu", GPR32Opnd>, ADD_FM_MM<0, 0x150>;
  def SUBu_MM  : MMRel, ArithLogicR<"subu", GPR32Opnd>, ADD_FM_MM<0, 0x1d0>;
  def MUL_MM   : MMRel, ArithLogicR<"mul", GPR32Opnd>, ADD_FM_MM<0, 0x210>;
  def ADD_MM   : MMRel, ArithLogicR<"add", GPR32Opnd>, ADD_FM_MM<0, 0x110>;
  def SUB_MM   : MMRel, ArithLogicR<"sub", GPR32Opnd>, ADD_FM_MM<0, 0x190>;
  def SLT_MM   : MMRel, SetCC_R<"slt", setlt, GPR32Opnd>, ADD_FM_MM<0, 0x350>;
  def SLTu_MM  : MMRel, SetCC_R<"sltu", setult, GPR32Opnd>,
                 ADD_FM_MM<0, 0x390>;
  def AND_MM   : MMRel, ArithLogicR<"and", GPR32Opnd, 1, IIAlu, and>,
                 ADD_FM_MM<0, 0x250>;
  def OR_MM    : MMRel, ArithLogicR<"or", GPR32Opnd, 1, IIAlu, or>,
                 ADD_FM_MM<0, 0x290>;
  def XOR_MM   : MMRel, ArithLogicR<"xor", GPR32Opnd, 1, IIAlu, xor>,
                 ADD_FM_MM<0, 0x310>;
  def NOR_MM   : MMRel, LogicNOR<"nor", GPR32Opnd>, ADD_FM_MM<0, 0x2d0>;
  def MULT_MM  : MMRel, Mult<"mult", IIImul, GPR32Opnd, [HI0, LO0]>,
                 MULT_FM_MM<0x22c>;
  def MULTu_MM : MMRel, Mult<"multu", IIImul, GPR32Opnd, [HI0, LO0]>,
                 MULT_FM_MM<0x26c>;

  /// Shift Instructions
  def SLL_MM   : MMRel, shift_rotate_imm<"sll", uimm5, GPR32Opnd>,
                 SRA_FM_MM<0, 0>;
  def SRL_MM   : MMRel, shift_rotate_imm<"srl", uimm5, GPR32Opnd>,
                 SRA_FM_MM<0x40, 0>;
  def SRA_MM   : MMRel, shift_rotate_imm<"sra", uimm5, GPR32Opnd>,
                 SRA_FM_MM<0x80, 0>;
  def SLLV_MM  : MMRel, shift_rotate_reg<"sllv", GPR32Opnd>,
                 SRLV_FM_MM<0x10, 0>;
  def SRLV_MM  : MMRel, shift_rotate_reg<"srlv", GPR32Opnd>,
                 SRLV_FM_MM<0x50, 0>;
  def SRAV_MM  : MMRel, shift_rotate_reg<"srav", GPR32Opnd>,
                 SRLV_FM_MM<0x90, 0>;
  def ROTR_MM  : MMRel, shift_rotate_imm<"rotr", uimm5, GPR32Opnd>,
                 SRA_FM_MM<0xc0, 0>;
  def ROTRV_MM : MMRel, shift_rotate_reg<"rotrv", GPR32Opnd>,
                 SRLV_FM_MM<0xd0, 0>;

  /// Load and Store Instructions - aligned
  let DecoderMethod = "DecodeMemMMImm16" in {
    def LB_MM  : Load<"lb", GPR32Opnd>, MMRel, LW_FM_MM<0x7>;
    def LBu_MM : Load<"lbu", GPR32Opnd>, MMRel, LW_FM_MM<0x5>;
    def LH_MM  : Load<"lh", GPR32Opnd>, MMRel, LW_FM_MM<0xf>;
    def LHu_MM : Load<"lhu", GPR32Opnd>, MMRel, LW_FM_MM<0xd>;
    def LW_MM  : Load<"lw", GPR32Opnd>, MMRel, LW_FM_MM<0x3f>;
    def SB_MM  : Store<"sb", GPR32Opnd>, MMRel, LW_FM_MM<0x6>;
    def SH_MM  : Store<"sh", GPR32Opnd>, MMRel, LW_FM_MM<0xe>;
    def SW_MM  : Store<"sw", GPR32Opnd>, MMRel, LW_FM_MM<0x3e>;
  }

  /// Load and Store Instructions - unaligned
  def LWL_MM : LoadLeftRightMM<"lwl", MipsLWL, GPR32Opnd, mem_mm_12>,
               LWL_FM_MM<0x0>;
  def LWR_MM : LoadLeftRightMM<"lwr", MipsLWR, GPR32Opnd, mem_mm_12>,
               LWL_FM_MM<0x1>;
  def SWL_MM : StoreLeftRightMM<"swl", MipsSWL, GPR32Opnd, mem_mm_12>,
               LWL_FM_MM<0x8>;
  def SWR_MM : StoreLeftRightMM<"swr", MipsSWR, GPR32Opnd, mem_mm_12>,
               LWL_FM_MM<0x9>;

  /// Move Conditional
  def MOVZ_I_MM : MMRel, CMov_I_I_FT<"movz", GPR32Opnd, GPR32Opnd,
                  NoItinerary>, ADD_FM_MM<0, 0x58>;
  def MOVN_I_MM : MMRel, CMov_I_I_FT<"movn", GPR32Opnd, GPR32Opnd,
                  NoItinerary>, ADD_FM_MM<0, 0x18>;
  def MOVT_I_MM : MMRel, CMov_F_I_FT<"movt", GPR32Opnd, IIAlu>,
                  CMov_F_I_FM_MM<0x25>;
  def MOVF_I_MM : MMRel, CMov_F_I_FT<"movf", GPR32Opnd, IIAlu>,
                  CMov_F_I_FM_MM<0x5>;

  /// Move to/from HI/LO
  def MTHI_MM : MMRel, MoveToLOHI<"mthi", GPR32Opnd, [HI0]>,
                MTLO_FM_MM<0x0b5>;
  def MTLO_MM : MMRel, MoveToLOHI<"mtlo", GPR32Opnd, [LO0]>,
                MTLO_FM_MM<0x0f5>;
  def MFHI_MM : MMRel, MoveFromLOHI<"mfhi", GPR32Opnd, [HI0]>,
                MFLO_FM_MM<0x035>;
  def MFLO_MM : MMRel, MoveFromLOHI<"mflo", GPR32Opnd, [LO0]>,
                MFLO_FM_MM<0x075>;

  /// Multiply Add/Sub Instructions
  def MADD_MM  : MMRel, MArithR<"madd", 1>, MULT_FM_MM<0x32c>;
  def MADDU_MM : MMRel, MArithR<"maddu", 1>, MULT_FM_MM<0x36c>;
  def MSUB_MM  : MMRel, MArithR<"msub">, MULT_FM_MM<0x3ac>;
  def MSUBU_MM : MMRel, MArithR<"msubu">, MULT_FM_MM<0x3ec>;
}
