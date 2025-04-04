import VersoBlog
import WebDemo.Demo

open Verso Genre Blog Site Syntax

def title : String := "Automatic generalization of theorems and proofs"

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do

    return {{
      <html>
        <head>
          <meta charset="UTF-8"/>
          <title>{{ (← param (α := String) "title") }} " — " {{ title }}</title>
          {{← builtinHeader }}
          <link rel="icon" type="image/x-icon" href="/static/img/favicon.ico"/>
          <link rel="stylesheet" href="/static/style.css"/>
          <link rel="stylesheet" href="/static/navbar.css"/>
          <link rel="stylesheet" href="/static/navbar-colors.css"/>
          <script crossorigin="anonymous" src="https://code.jquery.com/jquery-2.2.4.js"></script>
          <script src="/static/build-nav.js"></script>
        </head>
        <body>
          <header>
            <div class="inner-wrap">
            <a class="logo" href="/">{{ title }}</a>
            {{ ← topNav }}
            </div>
          </header>
          <div class="main" role="main">
            <div class="wrap">
              {{ (← param "content") }}
            </div>
          </div>
        </body>
      </html>
    }}
  }
  |>.override #[] ⟨do return {{<div class="frontpage"><h1>{{← param "title"}}</h1> {{← param "content"}}</div>}}, id⟩

-- with CSS and images
-- def demoSite : Site := site Walkthrough.Blog / static "static" ← "Demo/static_files"  -- copy from static `Demo/static_files' to '_out/walkthroughsite/static'

/-- The following text strings are what determines the URL of each of the pages -/
def demoSite : Site := site WebDemo.Pages.DemoPages.Introduction /
  static "static" ← "WebDemo/static_files"
  "intro" WebDemo.Pages.DemoPages.Introduction
  "handling-repeated-constants" WebDemo.Pages.DemoPages.GeneralizingMultipleOccurrences
  "handling-dependent-constants" WebDemo.Pages.DemoPages.GeneralizingDependencies

def main := blogMain theme demoSite
