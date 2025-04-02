# lake clean
# lake build
# git config --global --unset https.proxy # cheap fix to error saying lake can't connect to github
rm -rf _out/walkthroughsite # clear old output
lake exe walkthrough --output _out/walkthroughsite # add new output
python3 -m http.server 8800 --directory _out/walkthroughsite # start webserver