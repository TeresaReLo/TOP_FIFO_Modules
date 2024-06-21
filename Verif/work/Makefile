.DEFAULT_GOAL	:= help
testbench=tb


clean:
	rm -rf xvlog* xelab* xsim.* xvlog.log xvlog.pb webtalk* tr_db* ana elab sim .Xil vivado* work* *.wdb 

cc: clean
	clear

ana: clean
	xvlog -sv -f list.f
	@touch ana
	@echo "Latest analyzed HDL:" > ana
	@date >> ana

elab: ana
	xelab -debug typical --relax ${testbench}
	@touch elab
	@echo "Latest elaborated HDL:" > elab
	@date >> elab

sim: elab
	xsim work.${testbench} -wdb wave.wdb -runall -sv_seed random
	@touch sim
	@echo "Latest simulated HDL:" > sim
	@date >> sim 


sim_gui: elab
	xsim work.${testbench} -gui -wdb wave.wdb -view wave.wcfg -runall 
	@touch sim
	@echo "Latest simulated HDL:" > sim
	@date >> sim


help:
	@echo "" 
	@echo "==== Basic Vivado Compile/Simulator makefile ======"
	@echo " Targets:"
	@echo "	ana    --> Analyzes the HDL file with xvlog command" 
	@echo "	elab   --> Elaborates de design with xelab command"
	@echo "	sim    --> Simulates the design with xsim command"
	@echo "	sim_gui--> Simulates the design with xsim command and open gui"
	@echo "	clean  --> Clean support files"
	@echo "	help   --> this help menu =)"
	@echo "" 

