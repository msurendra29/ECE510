// =======================================================================
//   Department of Electrical and Computer Engineering
//   Portland State University
//
//   Course name:  ECE 510 - Pre-Silicon Validation
//   Term & Year:  Spring 2016
//   Instructor :  Tareque Ahmad
//   Project Team: Surendra Maddula, Bharath Reddy Godi.
//
//   Project:      Hardware implementation of PDP8 
//                 Instruction Set Architecture (ISA) level simulator
//
//   Filename:     instr_decode_stub.sv
//   Description:  TBD
//   Created by:   Bharath Reddy Godi
//   Date:         May 23, 2016
//
//   Copyright:    Surendra Maddula, Bharath Reddy Godi
// =======================================================================

`timescale 1ns/1ps

`include "pdp8_pkg.sv"
import pdp8_pkg::*;

module instr_decode_stub
  (
   // Global inputs
   input clk,
   input reset_n,

   // From Execution unit
   input stall,
   input [`ADDR_WIDTH-1:0] PC_value,

   // To Execution unit (decode struct)
   output [`ADDR_WIDTH-1:0] base_addr,
   output pdp_mem_opcode_s pdp_mem_opcode,
   output pdp_op7_opcode_s pdp_op7_opcode
   );


   parameter SET = 1'b1, CLEAR = 1'b0, INCOMPLETE = 1'b0, COMPLETE = 1'b1;
   parameter 		    O_AND = 5'd0,
                            O_TAD = 5'd1,
                            O_ISZ = 5'd2,
                            O_DCA = 5'd3,
                            O_JMS = 5'd4,
                            O_JMP = 5'd5,
                            O_SIX = 5'd6,
                            O_NOP = 5'd7,
                            O_IAC = 5'd8,
                            O_RAL = 5'd9,
                            O_RTL = 5'd10,
                            O_RAR = 5'd11,
                            O_RTR = 5'd12,
                            O_CML = 5'd13,
                            O_CMA = 5'd14,
                            O_CIA = 5'd15,
                            O_CLL = 5'd16,
                            O_CLA1 = 5'd17,
                            O_CLA_CLL = 5'd18,
                            O_HLT = 5'd19,
                            O_OSR = 5'd20,
                            O_SKP = 5'd21,
                            O_SNL = 5'd22,
                            O_SZL = 5'd23,
                            O_SZA = 5'd24,
                            O_SNA = 5'd25,
                            O_SMA = 5'd26,
                            O_SPA = 5'd27,
                            O_CLA2 = 5'd28;

   // Define enums for the state machine
   enum {IDLE,
         READY,
         SEND_REQ,
         DATA_RCVD,
         INST_DEC,
         STALL,
         DONE } current_state, next_state;

   reg [`ADDR_WIDTH-1:0] int_base_addr; // Latched value of base address

   reg                   int_rd_req;    // internal signal to drive read request to memory for instr fetch
   reg [`ADDR_WIDTH-1:0] int_rd_addr;   // internal register to latch PC from EU used as memory address for next instr fetch

   reg [`DATA_WIDTH-1:0] int_rd_data;   // Internal register to latch data from memory

   reg [1:0]count;
   reg [4:0]opcode_count;
   reg START_INST, AND_COMPLETE, TAD_COMPLETE, ISZ_COMPLETE, DCA_COMPLETE, JMS_COMPLETE, JMP_COMPLETE, NOP_COMPLETE, CLA_CLL_COMPLETE;
   reg [4:0]ran1;

   integer i;

   pdp_mem_opcode_s int_pdp_mem_opcode,ran_pdp_mem_opcode, A; // Internal struct to drive outut to Execution unit
   pdp_op7_opcode_s int_pdp_op7_opcode,ran_pdp_op7_opcode; // Internal struct to drive outut to Execution unit


   always @(posedge reset_n)begin
   	int_pdp_mem_opcode <= '{0,0,0,0,0,0,9'bz};
   	int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
	int_base_addr <= `START_ADDRESS;

	repeat(2) @(posedge clk)begin
	   	int_pdp_mem_opcode = '{0,0,0,0,0,0,9'bz};
	   	int_pdp_op7_opcode = '{1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
	end
   end

   initial begin

	count = 0;
	i = 0;
	START_INST = INCOMPLETE;
	AND_COMPLETE = INCOMPLETE;
	TAD_COMPLETE = INCOMPLETE;
	ISZ_COMPLETE = INCOMPLETE;
	DCA_COMPLETE = INCOMPLETE;
	JMS_COMPLETE = INCOMPLETE;
	JMP_COMPLETE = INCOMPLETE;
	NOP_COMPLETE = INCOMPLETE;
	CLA_CLL_COMPLETE = INCOMPLETE;

	repeat(5000000) @(negedge stall)begin

		repeat(1) @(posedge clk);
			int_pdp_mem_opcode = '{0,0,0,0,0,0,9'bz};
			int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};

		repeat(2) @(posedge clk);

		if(START_INST == INCOMPLETE)begin

			ran1 = $urandom_range(29);
			//$display("%d",ran1);

			case(ran1)
			            O_AND    : int_pdp_mem_opcode    <= '{1,0,0,0,0,0,$urandom_range(4096)};
	                            O_TAD    : int_pdp_mem_opcode    <= '{0,1,0,0,0,0,$urandom_range(4096)};
	                            O_ISZ    : int_pdp_mem_opcode    <= '{0,0,1,0,0,0,$urandom_range(4096)};
	                            O_DCA    : int_pdp_mem_opcode    <= '{0,0,0,1,0,0,$urandom_range(4096)};
	                            O_JMS    : int_pdp_mem_opcode    <= '{0,0,0,0,1,0,$urandom_range(4096)};
	                            O_JMP    : int_pdp_mem_opcode    <= '{0,0,0,0,0,1,$urandom_range(4096)};
	                            O_SIX    : int_pdp_mem_opcode <= '{0,0,0,0,0,0,9'bz};//
	                            O_NOP    : int_pdp_op7_opcode <= '{1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
	                            O_IAC    : int_pdp_op7_opcode <= '{0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
	                            O_RAL    : int_pdp_op7_opcode <= '{0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
	                            O_RTL    : int_pdp_op7_opcode <= '{0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
	                            O_RAR    : int_pdp_op7_opcode <= '{0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
	                            O_RTR    : int_pdp_op7_opcode <= '{0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
	                            O_CML    : int_pdp_op7_opcode <= '{0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
	                            O_CMA    : int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
	                            O_CIA    : int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0};
	                            O_CLL    : int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0};
	                            O_CLA1   : int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0};
	                            O_CLA_CLL: int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0};
	                            O_HLT    : int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0};
	                            O_OSR    : int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0};
	                            O_SKP    : int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0};
	                            O_SNL    : int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0};
	                            O_SZL    : int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0};
	                            O_SZA    : int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0};
	                            O_SNA    : int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0};
	                            O_SMA    : int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0};
	                            O_SPA    : int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0};
	                            O_CLA2   : int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1};
				    default:begin int_pdp_mem_opcode <= '{0,0,0,0,0,0,12'bz};//
	                         		int_pdp_op7_opcode <= '{1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};end
			endcase

			if(ran1 == 5'd6)begin
				int_pdp_op7_opcode <= '{1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			end
			else if(ran1 < 5'd6)begin
				int_pdp_op7_opcode <= '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			end
			else if(5'd30 < ran1 > 5'd6)begin
				int_pdp_mem_opcode    <= '{0,0,0,0,0,0,9'bz};
			end

			$display("@%2dns int_pdp_mem_opcode = %p, int_pdp_op7_opcode = %p",$time, int_pdp_mem_opcode, int_pdp_op7_opcode);

			i = i + 1;
			if(i == 200)begin
				i = 0;
				START_INST = COMPLETE;
				$display("********************START_INST**************************");
			end
		end

		else if(AND_COMPLETE == INCOMPLETE)begin
			//int_pdp_mem_opcode = '{1,0,0,0,0,0,$urandom_range(4096)};

			i = i + 1;
			if(i == 100)begin
				i = 0;
				AND_COMPLETE = COMPLETE;
				$display("********************AND_COMPLETE**************************");
				int_pdp_mem_opcode = '{1,0,0,0,0,0,$urandom_range(4096)};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};

				repeat(2)@(posedge clk);

				int_pdp_mem_opcode = '{0,0,0,0,0,1,$urandom_range(4096)};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			end

			else if((i == 10) ||(i == 30))begin
				int_pdp_mem_opcode = '{1,0,0,0,0,0,12'o1010};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			end

			else if((i == 20) ||(i == 40))begin
				int_pdp_mem_opcode = '{1,0,0,0,0,0,12'o1717};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			end
			
			else begin
				int_pdp_mem_opcode = '{1,0,0,0,0,0,$urandom_range(4096)};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			end
			$display("@%2dns int_pdp_mem_opcode = %p, int_pdp_op7_opcode = %p",$time, int_pdp_mem_opcode, int_pdp_op7_opcode);
		end

		else if(TAD_COMPLETE == INCOMPLETE)begin

			i = i + 1;
			if(i == 100)begin
				i = 0;
				TAD_COMPLETE = COMPLETE;
				$display("********************TAD_COMPLETE**************************");
				int_pdp_mem_opcode = '{0,1,0,0,0,0,$urandom_range(4096)};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};

				repeat(2)@(posedge clk);

				int_pdp_mem_opcode = '{0,0,0,0,0,1,$urandom_range(4096)};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			end

			else if((i == 10) ||(i == 30))begin
				int_pdp_mem_opcode = '{0,1,0,0,0,0,12'o1010};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			end

			else if((i == 20) ||(i == 40))begin
				int_pdp_mem_opcode = '{0,1,0,0,0,0,12'o1717};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			end
			
			else begin
				int_pdp_mem_opcode = '{0,1,0,0,0,0,$urandom_range(4096)};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			end
			$display("@%2dns int_pdp_mem_opcode = %p, int_pdp_op7_opcode = %p",$time, int_pdp_mem_opcode, int_pdp_op7_opcode);
		end

		else if(ISZ_COMPLETE == INCOMPLETE)begin

			i = i + 1;

			if(i == 100)begin
				i = 0;
				ISZ_COMPLETE = COMPLETE;
				$display("********************ISZ_COMPLETE**************************");
				int_pdp_mem_opcode = '{0,0,1,0,0,0,$urandom_range(4096)};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};

				repeat(2)@(posedge clk);

				int_pdp_mem_opcode = '{0,0,0,0,0,1,$urandom_range(4096)};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			end

			else if((i == 10) ||(i == 30))begin
				int_pdp_mem_opcode = '{0,0,1,0,0,0,12'o1010};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			end

			else if((i == 20) ||(i == 40))begin
				int_pdp_mem_opcode = '{0,0,1,0,0,0,12'o1717};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			end
			
			else begin
				int_pdp_mem_opcode = '{0,0,1,0,0,0,$urandom_range(4096)};
				int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			end
			$display("@%2dns int_pdp_mem_opcode = %p, int_pdp_op7_opcode = %p",$time, int_pdp_mem_opcode, int_pdp_op7_opcode);
		end

		else if(DCA_COMPLETE == INCOMPLETE)begin
			int_pdp_mem_opcode = '{0,0,0,1,0,0,$urandom_range(4096)};
			int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			i = i + 1;
			$display("@%2dns int_pdp_mem_opcode = %p, int_pdp_op7_opcode = %p",$time, int_pdp_mem_opcode, int_pdp_op7_opcode);
			if(i == 50)begin
				i = 0;
				DCA_COMPLETE = COMPLETE;
				$display("********************DCA_COMPLETE**************************");
			end

		end

		else if(JMS_COMPLETE == INCOMPLETE)begin
			int_pdp_mem_opcode = '{0,0,0,0,1,0,$urandom_range(4096)};
			int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			i = i + 1;
			$display("@%2dns int_pdp_mem_opcode = %p, int_pdp_op7_opcode = %p",$time, int_pdp_mem_opcode, int_pdp_op7_opcode);
			if(i == 50)begin
				i = 0;
				JMS_COMPLETE = COMPLETE;
				$display("********************JMS_COMPLETE**************************");
			end

		end

		else if(JMP_COMPLETE == INCOMPLETE)begin
			int_pdp_mem_opcode = '{0,0,0,0,0,1,$urandom_range(4096)};
			int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			i = i + 1;
			$display("@%2dns int_pdp_mem_opcode = %p, int_pdp_op7_opcode = %p",$time, int_pdp_mem_opcode, int_pdp_op7_opcode);
			if(i == 50)begin
				i = 0;
				JMP_COMPLETE = COMPLETE;
				$display("********************JMP_COMPLETE**************************");
			end

		end

		else if(NOP_COMPLETE == INCOMPLETE)begin
			int_pdp_mem_opcode = '{0,0,0,0,0,0,9'bz};
			int_pdp_op7_opcode = '{1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
			i = i + 1;
			$display("@%2dns int_pdp_mem_opcode = %p, int_pdp_op7_opcode = %p",$time, int_pdp_mem_opcode, int_pdp_op7_opcode);
			if(i == 50)begin
				i = 0;
				NOP_COMPLETE = COMPLETE;
				$display("********************NOP_COMPLETE**************************");
			end
		end

		else if(CLA_CLL_COMPLETE == INCOMPLETE)begin
			int_pdp_mem_opcode = '{0,0,0,0,0,0,9'bz};
			int_pdp_op7_opcode = '{0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0};
			i = i + 1;
			$display("@%2dns int_pdp_mem_opcode = %p, int_pdp_op7_opcode = %p",$time, int_pdp_mem_opcode, int_pdp_op7_opcode);
			if(i == 50)begin
				i = 0;
				CLA_CLL_COMPLETE = COMPLETE;
				$display("********************CLA_CLL_COMPLETE**************************");
			end
		end

	end
   end


   

   // Continuous assignment for the outputs to exec unit
   assign base_addr       = int_base_addr;
   assign pdp_mem_opcode  = int_pdp_mem_opcode;
   assign pdp_op7_opcode  = int_pdp_op7_opcode;

endmodule //  instr_decode

