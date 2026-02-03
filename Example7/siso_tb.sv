//------------------------------------------------------------------------------
//File       : siso_tb.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 03-02-2026
//Module     : tb
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: Serial In Serial Out Shift Register used for basic functional coverage example.
//------------------------------------------------------------------------------

`timescale 1ns/1ps

module tb;
  logic clk = 0, rst, si, so;
  
  siso dut(.*);
  
  always #5 clk = ~clk;
  
  logic [3:0] q_ref = 0; 
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    
    rst = 1; si = 0;
    #10;
    rst = 0;
    
    repeat(20) begin
      si = $urandom();
      
      q_ref = {q_ref[2:0], si};
      
      @(posedge clk); 
      #1;
      
      if (so !== q_ref[3]) 
        $error("Mismatch! Time=%0t DUT=%b Ref=%b", $time, so, q_ref[3]);
      else
        $display("Match! Time=%0t so=%b", $time, so);
    end
    
    $finish;
  end
endmodule
