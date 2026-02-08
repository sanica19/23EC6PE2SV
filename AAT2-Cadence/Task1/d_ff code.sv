//------------------------------------------------------------------------------
// File       : d_ff code.sv
// Author     : Sanica M S/ 1BM23EC229
// Project    : SystemVerilog and Verification (23EC6PE2SV)
// Description: d_ff
//------------------------------------------------------------------------------

//rtl code
module D_FF(D_inter.RTL1 rtl1);
always@(posedge rtl1.clk, posedge rtl1.reset)
begin
if(rtl1.reset)
rtl1.q<=0;
else if(rtl1.set)
rtl1.q<=1;
else
rtl1.q<=rtl1.d;
end
endmodule

//testbench
module test (D_inter.test1 t1);

initial begin
    // VCD dump setup
    $dumpfile("test.vcd");      // name of the VCD file
    $dumpvars(0, test);         // dump all signals in this module and below

    // Stimulus
    t1.reset = 0; 
    t1.set   = 0;
    t1.d     = 0;

    #10
    t1.reset = 1; 
    t1.set   = 1;
    t1.d     = 0;

    #10
    t1.reset = 0;
    t1.d     = 0;

    #10
    t1.d     = 1; 
    t1.set   = 0;

    #10
    t1.d     = 0;

    #10
    t1.d     = 1;

    #10
    t1.d     = 0;

    #100
    $finish;
end

endmodule

//interface
interface D_inter(input bit clk);
logic d,reset,set;
logic q;
modport RTL1(input clk, d,reset,set, output q);
modport test1(input q,output d, reset,set);
endinterface: D_inter

//top module
module top;
bit clk;
D_inter i1(clk);
D_FF Dut(i1);
test T1(i1);
always #5 clk=~clk;
initial
begin
$dumpfile("top.vcd");
$dumpvars;
$monitor("time=%d, clk=%b, reset=%b,set=%b, d=%b, q=%b", $time, clk, i1.reset, i1.set, 
i1.d, i1.q);
end
endmodule 
