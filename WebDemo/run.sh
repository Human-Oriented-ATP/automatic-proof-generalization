# lake clean
# lake build
# git config --global --unset https.proxy # cheap fix to error saying lake can't connect to github
cd .. # run from main directory of repo
rm -rf _out/webdemopage # clear old output
lake exe webdemo --output _out/webdemopage # add new output
python3 -m http.server 8800 -d _out/webdemopage # start webserver