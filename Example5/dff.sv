//------------------------------------------------------------------------------
//File       : dff.sv
//Author     :Sanica M S/1BM23EC229
//Created    : 03-02-2026
//Module     : dff
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: D Flip Flop used for basic functional coverage example.
//------------------------------------------------------------------------------

module dff(
	input clk, rst, d,
  output reg q
);
  always_ff @(posedge clk or posedge rst) begin
    if(rst)
      q <= 0;
    else
      q <= d;
  end
endmodule
