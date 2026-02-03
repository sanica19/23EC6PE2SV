//------------------------------------------------------------------------------
//File       : traffic_tb.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 03-02-2026
//Module     : tb
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: Traffic Light Controller used for basic functional coverage example.
//------------------------------------------------------------------------------

`timescale 1ns/1ps

import traffic_pkg::*;

module tb;
  logic clk = 0, rst;
  
  light_t colour;
  
  traffic dut(.*);
  
  always #5 clk = ~clk;
  
  covergroup cg_light @(posedge clk);
    cp_c: coverpoint colour {
      // Transition bin: Checks if we followed the specific sequence
      bins cycle = (RED => GREEN => YELLOW => RED);
    }
  endgroup
  
  //Declare handle here.
  cg_light cg;
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    
    cg = new();
    
    rst = 1; 
    @(posedge clk); 
    rst = 0;
    
    // Wait enough cycles for the full transition (R -> G -> Y -> R)
    repeat(10) @(posedge clk);

    $display("Coverage: %0.2f %%", cg.get_inst_coverage());
    $finish;
  end
endmodule
